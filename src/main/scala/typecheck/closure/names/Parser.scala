package typecheck.closure.names

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
    x == "let" || x == "in" || x == "λ" || x == "U"

  def pIdent: Parser[String] = for {
    x <- """[a-zA-Z_][a-zA-Z0-9_]*""".r
    _ <- if keyword(x) then failure(s"$x is keyword") else success(())
  } yield x

  def pKeyword(kw: String): Parser[Unit] = symbol(kw) >> { s =>
    not("""[a-zA-Z0-9_]""".r) | ws
  }

  def pAtom: Parser[Term] =
    pIdent ^^ Term.Var.apply | symbol("U") ^^^ Term.U | parens(pTerm)

  def pBinder: Parser[String] = pIdent | symbol("_")

  def pSpine: Parser[Term] = rep1(pAtom) ^^ { atoms =>
    atoms.reduceLeft(Term.App.apply)
  }

  def pLam: Parser[Term] = for {
    _ <- char('λ') | char('\\')
    xs <- rep1(pBinder)
    _ <- char('.')
    t <- pTerm
  } yield xs.foldRight(t)(Term.Lam.apply)

  def pPi: Parser[Term] = for {
    dom <- rep1(parens(rep1(pBinder) ~ (char(':') ~> pTerm)))
    _ <- pArrow
    cod <- pTerm
  } yield dom.foldRight(cod) { case ((params ~ a), t) =>
    params.foldRight(t)((param, acc) => Term.Pi(param, a, acc))
  }

  def funOrSpine: Parser[Term] = pSpine.flatMap { sp =>
    opt(pArrow).flatMap {
      case Some(_) => pTerm.map(t => Term.Pi("_", sp, t))
      case None    => success(sp)
    }
  }

  def pLet: Parser[Term] = for {
    _ <- pKeyword("let")
    x <- pBinder
    _ <- symbol(":")
    a <- pTerm
    _ <- symbol("=")
    t <- pTerm
    _ <- symbol(";")
    u <- pTerm
  } yield Term.Let(x, a, t, u)

  def pTerm: Parser[Term] = pLam | pLet | pPi | funOrSpine

  def pSrc: Parser[Term] = ws ~> pTerm <~ """\z""".r

  // Main function to parse input
  def parseInput(input: String): Term =
    parse(pSrc, new CharSequenceReader(input)) match
      case Success(result, next) =>
        result
      case Failure(msg, next) =>
        throw new Exception(s"Parse failure: $msg")
      case Error(msg, next) =>
        throw new Exception(s"Parse error: $msg")
}
