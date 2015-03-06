package at.logic.skeptik.algorithm.compressor.congruence


import at.logic.skeptik.congruence._

trait global {
  def globalAxioms = true
}

trait local {
  def globalAxioms = false
}

object ArrayCongruence extends CongruenceCompressor with ArrayStructure with subproofs with applyToAll

object FibonacciCongruence extends CongruenceCompressor with FibonacciStructure with subproofs with applyToAll

object ProofTreeCongruence extends CongruenceCompressor with ProofTreeStructure with subproofs with applyToAll

object FCnosub extends CongruenceCompressor with FibonacciStructure with outSubproofs with applyToAll

object FCtheory extends CongruenceCompressor with FibonacciStructure with subproofs with applyToTheory

object FCnosubtheory extends CongruenceCompressor with FibonacciStructure with outSubproofs with applyToTheory
