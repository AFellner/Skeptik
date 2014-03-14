package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E


class EqualityInference(c: Sequent) 
extends SequentProofNode {
  override lazy val conclusion = c
}

object EqualityInference {
  def apply(conclusion: Sequent) = new EqualityInference(conclusion)
  def unapply(p: SequentProofNode) = p match {
    case p: EqualityInference => Some(p.conclusion)
    case _ => None
  }
}