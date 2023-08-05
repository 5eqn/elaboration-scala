package benchmark

import org.openjdk.jmh.annotations._
import prune.scope._

import java.util.concurrent.TimeUnit

@State(Scope.Thread)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.NANOSECONDS)
class PruneTyBench:
  def genTm(prun: Pruning): Term =
    prun.foldLeft(Term.U)((acc, m) =>
      val icit = m match
        case Mask.Keep(icit) => icit
        case _               => Icit.Expl
      Term.Pi("_", Term.U, acc, icit)
    )

  // len: 16
  val prun = List(
    Mask.Pruned,
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Pruned,
    Mask.Pruned,
    Mask.Keep(Icit.Expl),
    Mask.Pruned,
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Pruned,
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl),
    Mask.Keep(Icit.Expl)
  )
  val ty = eval(List(), genTm(prun))

  @Benchmark
  def elabZoo: Term = pruneTy(prun, ty)

  @Benchmark
  def elabScala: Term = pruneTy2(prun, ty)
