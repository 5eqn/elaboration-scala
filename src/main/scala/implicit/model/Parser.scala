package `implicit`.model

import scala.util.parsing.combinator.{Parsers, RegexParsers}
import scala.util.parsing.input.CharSequenceReader
import scala.language.postfixOps

object ScalaParser extends RegexParsers {
  def ws: Parser[Unit] = """\s*""".r ^^^ ()

  def lexeme[A](p: Parser[A]): Parser[A] = p <~ ws

  def symbol(s: String): Parser[String] = lexeme(s)

  def char(c: Char): Parser[String] = lexeme(c.toString)

  def parens[A](p: Parser[A]): Parser[A] = "(" ~> p <~ ")"

  def pArrow: Parser[String] = symbol("→") | symbol("->")

  def keyword(x: String): Boolean =
    x == "let" || x == "in" || x == "λ" || x == "U" || x == "_"

  def pIdent: Parser[String] = for {
    x <- """[a-zA-Z_][a-zA-Z0-9_]*""".r
    _ <- if keyword(x) then failure(s"$x is keyword") else success(())
  } yield x

  def pKeyword(kw: String): Parser[Unit] = symbol(kw) >> { s =>
    not("""[a-zA-Z0-9_]""".r) | ws
  }

  def pAtom: Parser[Raw] =
    pIdent ^^ Raw.Var.apply |
      symbol("U") ^^^ Raw.U |
      symbol("_") ^^^ Raw.Hole |
      parens(pRaw)

  def pBinder: Parser[String] = pIdent | symbol("_")

  def pSpine: Parser[Raw] = rep1(pAtom) ^^ { atoms =>
    atoms.reduceLeft(Raw.App.apply(_, _, Dst.Expl))
  }

  def pLam: Parser[Raw] = for {
    _ <- char('λ') | char('\\')
    xs <- rep1(pBinder)
    _ <- char('.')
    t <- pRaw
  } yield xs.foldRight(t)(Raw.Lam.apply(_, _, Src.Expl))

  def pPi: Parser[Raw] = for {
    dom <- rep1(parens(rep1(pBinder) ~ (char(':') ~> pRaw)))
    _ <- pArrow
    cod <- pRaw
  } yield dom.foldRight(cod) { case ((params ~ a), t) =>
    params.foldRight(t)((param, acc) => Raw.Pi(param, a, acc, Icit.Expl))
  }

  def funOrSpine: Parser[Raw] = pSpine.flatMap { sp =>
    opt(pArrow).flatMap {
      case Some(_) => pRaw.map(t => Raw.Pi("_", sp, t, Icit.Expl))
      case None    => success(sp)
    }
  }

  def pLet: Parser[Raw] = for {
    _ <- pKeyword("let")
    x <- pBinder
    _ <- symbol(":")
    a <- pRaw
    _ <- symbol("=")
    t <- pRaw
    _ <- symbol(";")
    u <- pRaw
  } yield Raw.Let(x, a, t, u)

  def pRaw: Parser[Raw] = pLam | pLet | pPi | funOrSpine

  def pSrc: Parser[Raw] = ws ~> pRaw <~ """\z""".r

  // Main function to parse input
  def parseInput(input: String): Raw =
    parse(pSrc, new CharSequenceReader(input)) match
      case Success(result, next) =>
        result
      case Failure(msg, next) =>
        throw new Exception(s"Parse failure: $msg")
      case Error(msg, next) =>
        throw new Exception(s"Parse error: $msg")
}
