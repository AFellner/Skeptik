package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.immutable.SetSequent


abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {

  def apply(proof: Proof[SequentProofNode]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
    if (edgesToDelete.isEmpty) proof else Proof(proof.foldDown(fixProofNodes(edgesToDelete)))
  }

}

// Intersection trait is defined in RPILU.scala

trait outIntersection
extends AbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
                                    edgesToDelete: EdgesToDelete ) : SetSequent =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      SetSequent()

}

trait conclusionSequent
extends AbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
                                    edgesToDelete: EdgesToDelete ) : SetSequent =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      node.conclusion.toSetSequent

}

object RecyclePivots
extends RecyclePivots with outIntersection

object RecyclePivotsWithIntersection
extends RecyclePivots with Intersection

object RecyclePivotsWithConclusionSequent
extends RecyclePivots with conclusionSequent

//object IdempotentRecyclePivotsWithIntersection
//extends RecyclePivots with Intersection with IdempotentAlgorithm[SequentProofNode]
