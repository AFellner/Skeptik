package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}

abstract class AbstractSubsumption 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode]
}

trait LeftRight {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = proof
}
trait RightLeft {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = new Proof(proof.root,false)
}

abstract class TopDownSubsumption extends AbstractSubsumption {
  
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    val nodeMap = new MMap[Sequent,SequentProofNode]

    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
        val subsumer = nodeMap.find( A => A._1.subsequentOf(node.conclusion))
        val subsMap = subsumer.map(a => a._2)
        
        subsMap.getOrElse({
          val newNode = fixNode(node,fixedPremises)
          nodeMap += (newNode.conclusion -> newNode)
          newNode
        })
      })
    })
  }
}

object TopDownLeftRightSubsumption extends TopDownSubsumption with LeftRight

object TopDownRightLeftSubsumption extends TopDownSubsumption with RightLeft

abstract class BottomUpSubsumption extends AbstractSubsumption {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean

  def apply(inputproof: Proof[SequentProofNode]) = {
    val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
    val nodeMap = new MSet[SequentProofNode]
    val replaced = new MSet[SequentProofNode]
    val resulted = new MSet[SequentProofNode]
    val resultedPremises = new MSet[SequentProofNode]
    
    val replaceNodes2 = new MMap[SequentProofNode,SequentProofNode]
    
    val visited = new MSet[SequentProofNode]
    val waiting = new MSet[SequentProofNode]
    val results = new MMap[SequentProofNode,SequentProofNode]
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val subsumed = nodeMap.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumed match {
        case None => nodeMap += node
        case Some(u) => {
//          println(u + " replaces <collect> " + node)
          replaceNodes(node) = u
        }
      }
    }
    

  
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      visited += node
      
      
      for (p <- fixedPremises if replaced contains p) println("this shouldn't happen!") // and is not happening
      
      if (replaceNodes.isDefinedAt(node)) {
        val replacement = replaceNodes(node)
//        println(replacement.hashCode() + " replaces <replace> " + node.hashCode())
        println(replacement+ " replaces <replace> " + node)
//        println(notAncestor(replacement,node) + " and " + notAncestor(node,replacement))
      }
      val n = replaceNodes.get(node) match {
        case Some(u) => {
//          println("replacing " + node + " by " + u)
          replaced += node
//          require(resulted contains u) // we shouldn't replace node if u has not been visited/fixed yet.
          u
        }
        case None => {
//          val realFixedPremises = fixedPremises.map(f => replaceNodes.getOrElse(f, f))
          fixNode(node,fixedPremises)
        }
      }
      
      
      
//      for (p <- n.premises if replaced contains p) println("this shouldn't happen!") // and it is not happening
//      
//      if (replaced contains n) println("this also shouldn't happen!") // and it is not happening
      
      // since the two bad things above are not happening, 
      // it seems that calls to replace are not returning anything that should have been replaced.
      
      // Let's test this hypothesis once again by tracking everything (nodes and their premises) that is returned by calls to replace
      resulted += n
      for (p <- n.premises) resultedPremises += p
      
      for ((n1,n2) <- replaceNodes if n2 eq node) replaceNodes(n1) = n
      if (!(n eq node)) {
        replaceNodes += (node -> n)
//        println("replace " + node + " by " + n)
      }
      n
    }
    
    def checkReplaced(node: SequentProofNode, fixedPremises: Seq[Unit]):Unit = {
      if (replaced contains node) { // this shouldn't happen, but it is happening
        println("replaced node still occurs")
        println(node)
        println("replaced node: " + node.getClass())
        // if replaced contains node and this was caused by bugs in "replace",
        // then one of the following two conditions should be true. But, mysteriously, they are not!
        if (resulted contains node) println("replaced node was resulted from a call to replace)")
        if (resultedPremises contains node) println("replaced node was resulted as a premise from a call to replace")
        
        // therefore, I think that maybe something is going wrong not in "replace", 
        // but in the interaction of "replace" with "foldDown". 
        // In other words, "replace" is not resulting any replaced node 
        // (neither as the returned node nor as a premise of the returned node),
        // but somehow, "proof foldDown replace" still contains replaced nodes.
        
        //println("children: " + for )
        println()
      }
    }
    
    def childrenOfReplaced(node: SequentProofNode, results: Seq[Boolean]) = {
      val r = (replaced contains node)
      if (results contains true) {
        println("surviving replaced parent")
        println(node.getClass())
        println(results.head == true)
        println(node.conclusion)
      }
      r
    }
    
    val proof = setTraverseOrder(inputproof)

    proof bottomUp collect
//    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      if (replaceNodes.isDefinedAt(node)) println("bla")
//      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
//    })})
    
    def normalize() = {
//      println("NORMALIZE")
      for ((n1,n2) <- replaceNodes) {
        var last = n2
        while (replaceNodes contains last) last = replaceNodes(last)
        replaceNodes(n1) = last
//        println("n1  : " + n1.hashCode())
//        println("n2  : " + n2.hashCode())
//        println("last: " + last.hashCode())
//        println()
      }
    }
//    normalize()
//    replaceNodes.foreach(A => (println(A._1 + " <-- " + A._2)))
//    val outRoot = proof.foldDown2(replace)(replaced)
    val out = Proof(proof.foldDown(replace))
    out foldDown checkReplaced
//    println(outRoot.conclusion)
//    outRoot match {
//      case R(l,r,p,_) => {
//        println("pivot: " + p)
//        println("root: " + outRoot.hashCode())
//        println("root conclusion: " + outRoot.conclusion)
//        println("left: " + l.hashCode())
//        println("left conclusion: " + l.conclusion)
//        println("right: " + r.hashCode())
//        println("right conclusion: " + r.conclusion)
//      }
//    }
    //println("Is a node that should have been replaced still reachable from the root of output proof? : " + outRoot.existsAmongAncestors(n => replaced contains n))
//    out foldDown checkReplaced
//    println()
    //Proof(out.root) foldDown checkReplaced
    //out foldDown childrenOfReplaced
    //println()
    //proof foldDown childrenOfReplaced
    out
  }
}

abstract class BottomUpSubsumptionTime extends BottomUpSubsumption {
  val ancestors = new MMap[SequentProofNode,ISet[SequentProofNode]]
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(ancestors.getOrElse(node, {Proof(node) foldDown collectAncestors; ancestors(node)}) contains ancestor)
  }
  
  def collectAncestors(node: SequentProofNode, premises: Seq[SequentProofNode]):SequentProofNode = {
    ancestors(node) = (ISet(node) /: premises){ (l1,l2) =>
      l1 union ancestors(l2)
    }
//    print("#ancestors of " + node + " " + ancestors(node).size + "\n")
    //ancestors(node).foreach(println)
    node
  }
}

object BottomUpLeftRightSubsumptionTime extends BottomUpSubsumptionTime with LeftRight
object BottomUpRightLeftSubsumptionTime extends BottomUpSubsumptionTime with RightLeft

abstract class BottomUpSubsumptionMemory extends BottomUpSubsumption {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(node existsAmongAncestors {_ eq ancestor})
  }
}

object BottomUpLeftRightSubsumptionMemory extends BottomUpSubsumptionMemory with LeftRight
object BottomUpRightLeftSubsumptionMemory extends BottomUpSubsumptionMemory with RightLeft

abstract class AxiomSubsumption extends AbstractSubsumption {
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    val axioms = MMap[Sequent,SequentProofNode]()
    Proof(proof foldDown { (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case Axiom(conclusion) => {
        val subsumed = axioms.find(A => A._1 subsequentOf conclusion)
        val subsMap = subsumed.map(A => A._2)
        subsMap.getOrElse({axioms += (conclusion -> node); node})
      }
      case R(left, right, pivot, _) => fixNode(node,pivot,left,right,fixedPremises)
      case _ => node
    }})
  }
}

object LeftRightAxiomSubsumption extends AxiomSubsumption with LeftRight
object RightLeftAxiomSubsumption extends AxiomSubsumption with RightLeft
