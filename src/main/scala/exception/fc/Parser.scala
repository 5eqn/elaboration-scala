package exception.fc

import scala.util.parsing.combinator.{Parsers, RegexParsers}
import scala.util.parsing.input.CharSequenceReader
import scala.language.postfixOps

object ScalaParser extends RegexParsers {
  def ws: Parser[Unit] = ("""\s*""".r ^^^ ()) ~> comment
  def comment: Parser[Unit] = (("--.*".r ^^^ ()) ~> ws | success(()))
  def lexeme[A](p: Parser[A]): Parser[A] = p <~ ws
  def symbol(s: String): Parser[String] = lexeme(s)
  def char(c: Char): Parser[String] = lexeme(c.toString)
  def parens[A](p: Parser[A]): Parser[A] = "(" ~> p <~ ")"
  def braces[A](p: Parser[A]): Parser[A] = "{" ~> p <~ "}"
  def pArrow: Parser[String] = symbol("→") | symbol("->")
  def pBind: Parser[String] = pIdent | symbol("_")
  def keyword(x: String): Boolean =
    x == "let" || x == "in" || x == "λ" || x == "U" || x == "_"
  def pIdent: Parser[String] = for {
    x <- """[a-zA-Z_][a-zA-Z0-9_]*""".r
    _ <- if keyword(x) then failure(s"$x is keyword") else success(())
  } yield x
  def pKeyword(kw: String): Parser[Unit] = symbol(kw) >> { s =>
    not("""[a-zA-Z0-9_]""".r) | ws
  }

  // adding `positioned` is enough!
  def pAtom: Parser[Raw] = positioned(
    pIdent ^^ Raw.Var.apply |
      symbol("U") ^^^ Raw.U |
      symbol("_") ^^^ Raw.Hole |
      parens(pRaw)
  )

  def pDstImplBind = for {
    x <- "{" ~> pIdent <~ "="
    t <- pRaw <~ "}"
  } yield (t, Dst.ImplBind(x))
  def pDstImplAuto = for {
    _ <- "{"
    t <- pRaw <~ "}"
  } yield (t, Dst.ImplAuto)
  def pDstExpl = for {
    t <- pAtom
  } yield (t, Dst.Expl)
  def pArg: Parser[(Raw, Dst)] = pDstImplBind | pDstImplAuto | pDstExpl
  def pSpine: Parser[Raw] = positioned(for {
    atom <- pAtom
    args <- rep(pArg)
  } yield args.foldLeft(atom) { case (func, (arg, dst)) =>
    Raw.App(func, arg, dst)
  })

  def pSrcImplBind = for {
    x <- "{" ~> pIdent <~ "="
    t <- pBind <~ "}"
  } yield (t, Src.ImplBind(x))
  def pSrcImplAuto = for {
    t <- "{" ~> pBind <~ "}"
  } yield (t, Src.ImplAuto)
  def pSrcExpl = pBind ^^ ((_, Src.Expl))
  def pLamBinder = pSrcImplBind | pSrcImplAuto | pSrcExpl
  def pLam: Parser[Raw] = positioned(for {
    _ <- char('λ') | char('\\')
    xs <- rep1(pLamBinder)
    _ <- char('.')
    t <- pRaw
  } yield xs.foldRight(t)((param, rest) => Raw.Lam(param._1, rest, param._2)))

  def pPiExpl = parens(rep1(pBind) ~ (char(':') ~> pRaw)) ~ success(Icit.Expl)
  def pPiImpl = braces(rep1(pBind) ~ (char(':') ~> pRaw)) ~ success(Icit.Impl)
  def pPiImplAuto = braces(rep1(pBind) ~ success(Raw.Hole)) ~ success(Icit.Impl)
  def pPiBinder = pPiImpl | pPiImplAuto | pPiExpl
  def pPi: Parser[Raw] = positioned(for {
    dom <- rep1(pPiBinder)
    _ <- pArrow
    cod <- pRaw
  } yield dom.foldRight(cod) { case ((params ~ a ~ icit), t) =>
    params.foldRight(t)((param, acc) => Raw.Pi(param, a, acc, icit))
  })
  def funOrSpine: Parser[Raw] = positioned(pSpine.flatMap { sp =>
    opt(pArrow).flatMap {
      case Some(_) => pRaw.map(t => Raw.Pi("_", sp, t, Icit.Expl))
      case None    => success(sp)
    }
  })

  def pLet: Parser[Raw] = positioned(for {
    x <- pKeyword("let") ~> pIdent
    a <- opt(symbol(":") ~> pRaw)
    t <- symbol("=") ~> pRaw
    u <- symbol(";") ~> pRaw
  } yield Raw.Let(x, a.getOrElse(Raw.Hole), t, u))
  def pRaw: Parser[Raw] = pLam | pLet | pPi | funOrSpine
  def pSrc: Parser[Raw] = ws ~> pRaw <~ """\z""".r

  def parseInput(input: String): Raw =
    parse(pSrc, new CharSequenceReader(input)) match
      case Success(result, next) =>
        result
      case Failure(msg, next) =>
        throw new Exception(s"Parse failure: $msg")
      case Error(msg, next) =>
        throw new Exception(s"Parse error: $msg")
}
