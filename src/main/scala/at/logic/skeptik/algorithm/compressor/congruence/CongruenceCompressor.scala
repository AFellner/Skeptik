package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.util.io.FileOutput
import at.logic.skeptik.expression.{E,App}
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import at.logic.skeptik.congruence.AbstractCongruence
import at.logic.skeptik.congruence.structure.{EqW,EquationPath}

/**
 * abstract class CongruenceCompressor traverses the proof while searching for nodes, 
 * with a compressable congruence reasoning part.
 * Such nodes contain a redundant explanation, which is replaced by a shorter one.
 * For details see Thesis Space & Congruence Compression of Proofs
 * 
 * it is instantiated by a congruence closure procedure (ProofTree and two versions of EquationGraph)
 */

abstract class CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): AbstractCongruence
  
  def apply(proof: Proof[N]) = {
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()
    
    //Proof statistics output
//    val directory = "/global/lv70340/AFellner/explsize_13/"
//    val filename = this.getClass.getSimpleName + "_proof_"+proof.hashCode
//    val output = new FileOutput(directory + filename)
//    val header = "original, produced, theorylemma\n"
//    output.write(header)
    
    val lowTheoryLemma = MSet[N]();
    
    // TheoryLemma classification traversal for stricter node selection criteria
    
    def classifyNodes(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      if (fromPr.isEmpty) (node,node.isInstanceOf[TheoryAxiom])
      else {
        var theorylemma = fromPr.map(_._2).forall(b => b)
        if (!theorylemma) {
          lowTheoryLemma ++= fromPr.filter(b => b._2).map(_._1)
        }
        (node,theorylemma)
      }
    }
    
    // main traversal
    
    def traversal(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      if (fromPr.isEmpty) (node,node.isInstanceOf[TheoryAxiom])
      else {
        val fixedNode = fixNode(node,fromPr.map(_._1))
        var theorylemma = fromPr.map(_._2).forall(b => b)
        
        //A more selective criteria here should speed up the algorithm, 
        //possibly at the cost of less compression
//        val resNode = if (lowTheoryLemma.contains(node)) {
//        val resNode = if (true) {
        val resNode = if ((node.isInstanceOf[TheoryR] || node.isInstanceOf[TheoryAxiom]) && hasNonEqChild(node,proof)) {
//          println("Actually trying!: " + node.getClass)
          val rightEqs = fixedNode.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
          val leftEqs = fixedNode.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
//          println("bla1")
          val con = newCon.addAll(leftEqs)
          val eqToMap = rightEqs.map(eq => {
            val con2 = con.addNode(eq.l).addNode(eq.r).updateLazy
            con2.explain(eq.l,eq.r) match {
              case Some(path) => {
                path.toProof match {
                  case Some(proof) => {
//                    val newSize = proof.root.conclusion.ant.size
                    val leftEqsNew = proof.root.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
                    val newSize = leftEqsNew.size
                    val oldSize = leftEqs.size
//                    val line = oldSize + ", " + newSize + ", " + theorylemma + "\n"
//                    output.write(line)
//                    if (proof.size > 1) println("Proof is bigger than 1")
                    val axiom = path.toAxiom
                    if (newSize < oldSize) {// || (newSize == oldSize && proof.size < Proof(fixedNode).size)) {
//                      println("found a smaller one! class: " + node.getClass)
//                      val axiom = path.toAxiom
                      proof.root
//                      axiom
                    }
                    else fixedNode
                  }
                  case None => fixedNode
                }
              }
              case _ => fixedNode
            }
          })
          
          val x = if (eqToMap.isEmpty) {
            fixedNode 
          }
          else eqToMap.minBy(_.conclusion.size)
          x
        }
        else {
          fixedNode
        }
        (resNode,theorylemma)
      }
    }
//    proof foldDown classifyNodes
    
    val newProof = (proof foldDown traversal)._1

//    val resProof2 = newProof.conclusion.ant.foldLeft(newProof)({(A,B) => 
//      reflMap.get(B) match {
//        case Some(node) => R(A,node)
//        case None => A
//      }
//    })
    val resProof2 = newProof
    if (!resProof2.conclusion.isEmpty) println("Non empty proof")
//    println("proof: " + newProof)
    //DAGify is necessary to gain reasonable compression, due to recreation of some axioms in subproof production
    DAGify(resProof2)
  }
  
  def hasNonEqChild(node: N, proof: Proof[N]): Boolean = {
    proof.childrenOf(node).exists {c => !c.isInstanceOf[TheoryAxiom] && !c.isInstanceOf[TheoryR]}
  }
  
}