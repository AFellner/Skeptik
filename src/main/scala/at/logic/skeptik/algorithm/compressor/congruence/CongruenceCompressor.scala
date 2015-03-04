package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.util.io.FileOutput
import at.logic.skeptik.expression.{E,App}
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.immutable.{HashMap => IMap, HashSet => ISet}
import at.logic.skeptik.congruence.AbstractCongruence
import at.logic.skeptik.congruence.structure.{EqW,EquationPath}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

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
    implicit val nodeMap = MMap[Sequent,N]()
    val resWithMap = MMap[E,N]()
    
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
    
    def traversal(node: N, fromPr: Seq[(N,Set[EqW],Set[EqW],Set[EqW],IMap[E,N],Boolean)]): (N,Set[EqW],Set[EqW],Set[EqW],IMap[E,N],Boolean) = {
      val premiseFixed = if (fromPr.isEmpty) false else fromPr.map(_._6).max
      if (!premiseFixed) {
        val leftEqs = node.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
        val rightEqs = node.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
        
//        println("adding " + rightEqs.mkString(", ") + " from: " + node)
        
        val leftEqsPremise = fromPr.map(_._2).flatten.toSet
        val rightEqsPremise = fromPr.map(_._3).flatten.toSet
        val allAxiomsPremise = fromPr.map(_._4).flatten.toSet
        
        val allLeftEqs = leftEqsPremise ++ leftEqs
        val allRightEqs = rightEqsPremise ++ rightEqs
        val allAxioms = if (rightEqs.size == 1 && leftEqs.size == 0) allAxiomsPremise + rightEqs.last else allAxiomsPremise
        
        val resWithPremise = 
          if (fromPr.isEmpty) IMap[E,N]()
          else fromPr.map(_._5).tail.foldLeft(fromPr.map(_._5).head)({(A,B) => 
            A ++ B
          })
        
        //internal theory node -> enlarge sets
        if (!hasNonEqChild(node,proof)) {
//          val resWith = if (!rightEqs.isEmpty) resWithPremise + node else resWithPremise
//          val resWith = if (node.isInstanceOf[TheoryAxiom]) resWithPremise + node else resWithPremise
          
//          val resWith = {
//            if (rightEqs.size == 1 && !resWithPremise.isDefinedAt(rightEqs.last.equality)) 
//              resWithPremise + (rightEqs.last.equality -> node)
//            else resWithPremise
//          }
          val resWith = rightEqs.foldLeft(resWithPremise)({(A,B) =>
            A + (B.equality -> node)
          })
          (node,allLeftEqs,allRightEqs,allAxioms,resWith,false)
        }
        //low theory lemma
        else {
          val currentExplanation = leftEqs ++ allAxioms
          val con = newCon.addAll(currentExplanation)
          val eqToMap = rightEqs.map(eq => {
            val con2 = con.addNode(eq.l).addNode(eq.r).updateLazy
            con2.explain(eq.l,eq.r) match {
              case Some(path) => {
                if (path.originalEqs.size < currentExplanation.size) {
//                  println("Found a better explanation: ")
//                  println(path.originalEqs.mkString(", "))
//                  println(currentExplanation.mkString(", "))
                  path.toProof match {
                    case Some(localProof) => {
                      val finalProof = localProof.root.conclusion.ant.filter(EqW.isEq(_)).foldLeft(localProof.root)({(A,B) => 
                        if (resWithPremise.isDefinedAt(B)) {
//                          println("Having something to resolve against")
                          try {
                            R(resWithPremise(B),A)
                          }
                          catch {
                            case e:Exception => {
                              println(A.conclusion + " not resolavable with:\n" + resWithPremise(B) + "\nliteral is supposed to be: " + B)
                              throw(e)
                            }
                          }
                        }
                        else A
                      })
                      replaceInNodeMap(localProof.root,nodeMap)
                    }
                    case None => replaceInNodeMap(node,nodeMap)
                  }
                }
                else replaceInNodeMap(node,nodeMap)
              }
              case _ => replaceInNodeMap(node,nodeMap)
            }
          })
          
          val x = if (eqToMap.isEmpty) {
            replaceInNodeMap(node,nodeMap)
          }
          else eqToMap.minBy(_.conclusion.size)
//          val y = resWithPremise.foldLeft(x)({(A,B) => 
//            val out = try R(A,B)
//            catch {
//              case e: Exception => {
//                A
//              }
//            }
//            replaceInNodeMap(out,nodeMap)
//          })
          val y = x
//          if (Proof(y).size > Proof(node).size) {
//            println("proof got bigger by replacing; sizes: " + y.conclusion.size + " vs " + node.conclusion.size)
//          }
          replaceInNodeMap(y,nodeMap)
          (y,ISet(),ISet(),ISet(),IMap[E,N](),true)
        }
      }
      else {
        val fixedNode = fixNode(node,fromPr.map(_._1))
        val outNode = replaceInNodeMap(fixedNode,nodeMap)
        (outNode,ISet(),ISet(),ISet(),IMap[E,N](),true)
      }
    }
//    proof foldDown classifyNodes
    
    val newProof = (proof foldDown traversal)._1

    val resProof2 = newProof.conclusion.ant.foldLeft(newProof)({(A,B) => 
      reflMap.get(B) match {
        case Some(node) => replaceInNodeMap(R(A,node),nodeMap)
        case None => replaceInNodeMap(A,nodeMap)
      }
    })
    val finalProof = resProof2.conclusion.ant.foldLeft(resProof2)({(A,B) => 
      if (resWithMap.isDefinedAt(B)) {
        println("Having something to resolve against")
        R(resWithMap(B),A)
      }
      else A
    })
//    val resProof2 = newProof
    if (!finalProof.conclusion.isEmpty) println("Non empty proof" + finalProof)
//    resProof2
//    println("proof: " + newProof)
    //DAGify is necessary to gain reasonable compression, due to recreation of some axioms in subproof production
    DAGify(finalProof)
  }
  
  def replaceInNodeMap(node: N, nodeMap: MMap[Sequent,N]) = {
//    if (nodeMap.contains(node.conclusion)) {
//      val inMap = nodeMap(node.conclusion)
//      if (Proof(inMap).size > Proof(node).size) {
//        nodeMap.update(node.conclusion,node)
//        node
//      }
//      else inMap
//    }
//    else nodeMap += (node.conclusion -> node); node
    node
  }
  
  def hasNonEqChild(node: N, proof: Proof[N]): Boolean = {
    proof.childrenOf(node).exists {c => !c.isInstanceOf[TheoryAxiom] && !c.isInstanceOf[TheoryR]}
  }
  
}