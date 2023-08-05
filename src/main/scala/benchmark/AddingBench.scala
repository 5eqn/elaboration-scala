package benchmark

import org.openjdk.jmh.annotations._

import java.util.concurrent.TimeUnit

@State(Scope.Thread)
@BenchmarkMode(Array(Mode.AverageTime))
@OutputTimeUnit(TimeUnit.NANOSECONDS)
class AddingBench:
  val x = 1
  val y = 2

  @Benchmark
  def measureRight: Int = x + y
