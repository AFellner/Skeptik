package at.logic.skeptik.congruence

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.congruence._
import at.logic.skeptik.congruence.structure.EqW
import at.logic.skeptik.expression.E
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._

trait earlyRes {
  def resolveEarly: Boolean = true
}

trait lazyRes {
  def resolveEarly: Boolean = false
}

trait subproofs {
  def generateSubProofs = true
}

trait outSubproofs {
  def generateSubProofs = false
}

trait applyToTheory {
  def applyCriterion(node: N, proof: Proof[N]) = {
    node.isInstanceOf[TheoryAxiom] || node.isInstanceOf[TheoryR] || node.isInstanceOf[TheoryLemma]
  }
}

trait applyToAll {
  def applyCriterion(node: N, proof: Proof[N]) = {
    true
  }
}

trait ArrayStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    ArrayCon(eqReferences)
  }
}

trait FibonacciStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    FibCon(eqReferences)
  }
}

trait ProofTreeStructure {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    ProofTreeCon(eqReferences)
  }
}