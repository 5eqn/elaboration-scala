package benchmark

import org.openjdk.jmh.annotations._
import prune.scope._

import java.util.concurrent.TimeUnit

@State(Scope.Thread)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.NANOSECONDS)
class PruneVFlexBench:
  def genTm(prun: Pruning): Term =
    prun.foldLeft(Term.U)((acc, m) =>
      val icit = m match
        case Mask.Keep(icit) => icit
        case _               => Icit.Expl
      Term.Pi("_", Term.U, acc, icit)
    )
  def genSp(prun: Pruning): Spine =
    val filtered = prun.filter {
      case Mask.Keep(_) => true
      case _            => false
    }
    val len = filtered.length
    filtered
      .zip(0 until len)
      .map((mask, idx) =>
        mask match
          case Mask.Keep(i) => prune.scope.Param(Val.Var(len - idx - 1), i)
          case _            => throw new Exception("impossible")
      )
  def genPren(prun: Pruning): PartialRenaming =
    prun.foldRight(PartialRenaming(0, 0, Map(), None))((m, acc) =>
      m match
        case Mask.Keep(i) => acc.lift
        case Mask.Pruned  => acc.skip
    )

  // len: 16
  // uppermost element is rightmost param in Pi chain
  // and the uppermost element (rightmost param) of Spine
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
  val sp = genSp(prun)
  val pren = genPren(prun)

  @Benchmark
  def elabZoo: Term =
    Meta.init()
    val metaID = Meta.create(ty)
    pruneVFlex(pren, metaID, sp)

  @Benchmark
  def elabScala: Term =
    Meta.init()
    val metaID = Meta.create(ty)
    pruneVFlex2(pren, metaID, sp)
