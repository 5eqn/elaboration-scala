package commented

import scala.util.parsing.combinator.{Parsers, RegexParsers}
import scala.util.parsing.input.CharSequenceReader
import scala.language.postfixOps
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

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

  // minimal unit
  def pAtom = positioned(
    pIdent ^^ Raw.Var.apply |
      symbol("U") ^^^ Raw.U |
      symbol("_") ^^^ Raw.Hole |
      parens(pRaw)
  )

  // automatic hole insertion
  def pHole = positioned(success(Raw.Hole))

  // any of the below arguments
  def pArg = pDstImplBind | pDstImplAuto | pDstExpl

  // {arg = raw}
  def pDstImplBind = for {
    x <- "{" ~> pIdent <~ "="
    t <- pRaw <~ "}"
  } yield (t, Dst.ImplBind(x))

  // {raw}
  def pDstImplAuto = braces(pRaw) ^^ ((_, Dst.ImplAuto))

  // raw
  def pDstExpl = pAtom ^^ ((_, Dst.Expl))

  // atom raw0 {raw1} {arg2 = raw2} ...
  def pSpine = positioned(for {
    atom <- pAtom
    args <- rep(pArg)
  } yield args.foldLeft(atom) { case (func, (arg, dst)) =>
    Raw.App(func, arg, dst)
  })

  // any of the below lambda binders
  def pLamBinder =
    pSrcImplTyped | pSrcImplBind | pSrcImplAuto | pSrcExplTyped | pSrcExpl

  // {param = binder}
  def pSrcImplBind = for {
    x <- "{" ~> pIdent <~ "="
    t <- pBind <~ "}"
  } yield (t, None, Src.ImplBind(x))

  // {binder}
  def pSrcImplAuto = braces(pBind) ^^ ((_, None, Src.ImplAuto))

  // binder
  def pSrcExpl = pBind ^^ ((_, None, Src.Expl))

  // {binder : Raw}
  def pSrcImplTyped = for {
    x <- "{" ~> pBind <~ ":"
    t <- pRaw <~ "}"
  } yield (x, Some(t), Src.ImplAuto)

  // (binder : Raw)
  def pSrcExplTyped = for {
    x <- "(" ~> pBind <~ ":"
    t <- pRaw <~ ")"
  } yield (x, Some(t), Src.Expl)

  // \binder0 {param1 = binder1} (binder2 : Raw). raw
  def pLam = positioned(
    for {
      _ <- char('λ') | char('\\')
      xs <- rep1(pLamBinder)
      _ <- char('.')
      t <- pRaw
    } yield xs.foldRight(t)((param, rest) =>
      Raw.Lam(param._1, param._2, rest, param._3)
    )
  )

  // any of the below Pi binders
  def pPiBinder = pPiImpl | pPiImplAuto | pPiExpl

  // (binder1 binder2 : Raw)
  def pPiExpl = parens(rep1(pBind) ~ (char(':') ~> pRaw)) ~ success(Icit.Expl)

  // {binder1 binder2 : Raw}
  def pPiImpl = braces(rep1(pBind) ~ (char(':') ~> pRaw)) ~ success(Icit.Impl)

  // {binder1 binder2}
  def pPiImplAuto = braces(rep1(pBind) ~ pHole) ~ success(Icit.Impl)

  // (binder1 binder2 : Raw) -> {binder3} -> Raw
  def pPi = positioned(for {
    dom <- rep1(pPiBinder)
    _ <- pArrow
    cod <- pRaw
  } yield dom.foldRight(cod) { case ((params ~ a ~ icit), t) =>
    params.foldRight(t)((param, acc) => Raw.Pi(param, a, acc, icit))
  })

  // convert {A} {B} -> C to {A} -> {B} -> C
  def funOrSpine = positioned(pSpine.flatMap { sp =>
    opt(pArrow).flatMap {
      case Some(_) => pRaw.map(t => Raw.Pi("_", sp, t, Icit.Expl))
      case None    => success(sp)
    }
  })

  // ": Raw" or Nothing (yields a Hole)
  def pTy = (symbol(":") ~> pRaw) | pHole

  // let x : a = t; u
  def pLet = positioned(for {
    x <- pKeyword("let") ~> pIdent
    a <- pTy
    t <- symbol("=") ~> pRaw
    u <- symbol(";") ~> pRaw
  } yield Raw.Let(x, a, t, u))

  // an entire term
  def pRaw: Parser[Raw] = pLam | pLet | pPi | funOrSpine

  // the entire source file
  def pSrc = ws ~> pRaw <~ """\z""".r

  def parseInput(input: String): Raw =
    parse(pSrc, new CharSequenceReader(input)) match
      case Success(result, next) =>
        result.ensurePosed(next.pos)
        result
      case Failure(msg, next) =>
        throw new Exception(s"Parse failure: $msg")
      case Error(msg, next) =>
        throw new Exception(s"Parse error: $msg")
}
