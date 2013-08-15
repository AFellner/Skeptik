package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.mutable.Stack
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
  val nextNode = new Next[SequentProofNode]
  var replaceNode:Option[SequentProofNode] = None
  
  def apply(inputproof: Proof[SequentProofNode]) = {
    val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
    val nodeSet = new MSet[SequentProofNode]
    val replaced = new MSet[SequentProofNode]
    val resulted = new MSet[SequentProofNode]
    val fixed = new MSet[SequentProofNode]
    val resultedPremises = new MSet[SequentProofNode]
    val prints = false
    
    val jumpedTo = new MSet[SequentProofNode]
    
    val visited = new Stack[SequentProofNode]
//    val waiting = new MSet[SequentProofNode]
    val isWaitingFor = new MMap[SequentProofNode,MSet[SequentProofNode]]
    val finalResults = new MMap[SequentProofNode,SequentProofNode]
    
    val nodeStack = new Stack[SequentProofNode] 
    val originals = new MSet[SequentProofNode]
    
    val subsumed = new MSet[SequentProofNode]
//    inputproof.foreach(f => originals += f)
    
    def jumpTo2(from: SequentProofNode, to: SequentProofNode) {
      var n:SequentProofNode = null
      do {
        n = nodeStack.pop
//           println("remove waitingFor: " + n)
      } while (!(n eq to))
      nextNode.n = Some(from,to)
    }
      
//    var jump = false
    def replace2(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
//      if (jump) {
//        jump = false
//        println("arrive here: "+ node)
//      }

      nextNode.n = None
      replaceNode match {
        case None => {
          val subsumer = nodeStack.find( A => !(node eq A) && (node.conclusion subsequentOf A.conclusion) && (notAncestor(node,A)))
          
          nodeStack.push(node)
          val newNode = fixNode(node,fixedPremises)
          
          if (!(newNode eq node)) {
            if (subsumed contains node) println("subsumed changed again")
            replaced += node
          }
          if (subsumer.isDefined) {
            jumpTo2(node,subsumer.get)
            subsumed += node
            replaceNode = Some(newNode)
          } 
          newNode
        }
        case Some(n) => {
//          println("replacing " + node + " by " + n)
          replaced += node
          replaceNode = None
          n
        }
      }
        
    }
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val subsumed = nodeSet.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumed match {
        case None => nodeSet += node
        case Some(u) => {
//          println(u + " replaces <collect> " + node)
          replaceNodes(node) = u
        }
      }
    }
    
    def jumpTo(from: SequentProofNode, to: SequentProofNode) {
      var n:SequentProofNode = null
      do {
        n = visited.pop
        isWaitingFor -= n
//           println("remove waitingFor: " + n)
      } while (!(n eq to))
      if (prints) println("jumpting to " + to)
//        print(Proof(t))
      nextNode.n = Some(from,to)
    }
    var first = true
    var firstNode:SequentProofNode = null
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (first) firstNode = node
      visited.push(node)
      nextNode.n = None
      replaceNodes.get(node) match {
        case Some(u) => {
//          notAncestor(node,u)
          
          if (finalResults contains u) {
            replaced += node
            val finalU = finalResults(u)
            finalResults += (node -> finalU)
            updateReplace(node,finalU)
            updateResults(node,finalU)
            isWaitingFor -= node
            replaceNodes.map(A => A._2).find(A => A eq node).foreach(f => {
//              println("jump back to " + isWaitingFor.find(A => (A._2 contains f)).map(A => A._1).foreach(print))
              if (prints) println("jump because replace")
//              jumpTo(isWaitingFor.find(A => (A._2 contains f)).map(A => A._1))
            })
            if (prints) println(node + " get its final result " + finalU)
            finalU
          }
          else {
            if (prints) println(node + " waits because " + u + " does not have its final result")
            waitsFor(node,u)
            node
          }
        }
        case None => {
  //          val realFixedPremises = fixedPremises.map(f => replaceNodes.getOrElse(f, f))
          val waitingPremises = fixedPremises.filter(p => (isWaitingFor contains p))
          if (!(waitingPremises.isEmpty)){
//            if (prints) println(node + " waits, because one premise is waiting")
            waitingPremises.foreach(r => waitsFor(node,r))
            node
          }
          else {
//            if (prints) println(node + " is being fixed")
            val newNode = fixNode(node,fixedPremises)
            if (!(node eq newNode)) {
              updateReplace(node,newNode)
              updateWaitingFor2(node,newNode)
              normalize
//              replaced += node
              if (fixed contains node) {
                    println("fixed again")
  //                replaceNodes += (node -> newNode)
              }
//              replaceNodes.find(A => A._2 eq node).map(A => A._1).foreach(n => waitsFor(n,newNode))
            }
            val x = updateResults(node,newNode)
            finalResults += (node -> newNode)
//            normalizeResults
            isWaitingFor -= node
//            val firstNode = getFirstInResultChain(node)
            replaceNodes.map(A => A._2).find(A => A eq newNode).foreach(f => {
//              println("jump back to " + isWaitingFor.find(A => (A._2 contains f)).map(A => A._1).foreach(print))
//              if (prints) println("jump because fix")
//              jumpTo(isWaitingFor.find(A => (A._2 contains f) && (A._1.premises.forall(pr => !(isWaitingFor contains pr)))).map(A => A._1))
            })
            
            fixed += newNode
            newNode
          }
        }
      }
    }
    
    def getFirstInResultChain(node: SequentProofNode):SequentProofNode = {
      var last = node
      var opt = finalResults.find(A => A._2 eq last).map(A => A._1)
      while (!(opt eq None)) {
        last = opt.get
        opt = finalResults.find(A => A._2 eq last).map(A => A._1)
      }
      last
    }
    
    def updateReplace(node: SequentProofNode, byNode: SequentProofNode):SequentProofNode = {
      var out = node
      replaceNodes.foreach(R => {
        if (R._2 eq node) {
          replaceNodes -= R._1
          replaceNodes += (R._1 -> byNode)
          out = R._1
        }
      })
      out
    }
    def updateWaitingFor2(node: SequentProofNode, byNode: SequentProofNode) = {
      isWaitingFor.foreach(R => {
        if (R._2 contains node) {
          R._2 -= node
          R._2 += byNode
        }
      })
    }
    def updateResults(node: SequentProofNode, byNode: SequentProofNode):SequentProofNode =  {
      var out = node
      finalResults.foreach(R => {
        if (R._2 eq node) {
          finalResults -= R._1
          finalResults += (R._1 -> byNode)
          out = R._1
        }
      })
      out
    }
    def normalize() = {
      for ((n1,n2) <- replaceNodes) {
        var last = n2
        while (replaceNodes contains last) last = replaceNodes(last)
        replaceNodes(n1) = last
      }
    }
    
    def normalizeResults() = {
      for ((n1,n2) <- finalResults) {
        var last = n2
        while (finalResults contains last) last = finalResults(last)
        finalResults(n1) = last
      }
    }
    def addReason(node: SequentProofNode, reason: SequentProofNode) {
      if (isWaitingFor.isDefinedAt(node)) {
        isWaitingFor(node) += reason
      }
      else {
        isWaitingFor += (node -> MSet[SequentProofNode](reason))
      }
    }
    
    def updateWaitingFor(node: SequentProofNode) {
      if (isWaitingFor.isDefinedAt(node)) {
//        ancestors(node) = (ISet(node) /: premises){ (l1,l2) =>
//          l1 union ancestors(l2)
//        }
        isWaitingFor(node) = (isWaitingFor(node) /: isWaitingFor(node)) {(n1,n2) =>
          n1 union isWaitingFor.getOrElse(n2,MSet[SequentProofNode]())
        }
      }
    }
    
    def waitsFor(node:SequentProofNode, reason: SequentProofNode) {
      addReason(node,reason)
      updateWaitingFor(reason)
      updateWaitingFor(node)
//      println("isWaitingFor before: " + isWaitingFor(node))
//      isWaitingFor(node) = isWaitingFor(node) union isWaitingFor.getOrElse(reason, MSet[SequentProofNode]())
//      println("isWaitingFor after: " + isWaitingFor(node))
//      isWaitingFor(node).foreach{r => 
//        isWaitingFor.getOrElse(r, MSet[SequentProofNode]()).foreach(f => addReason(node,f))
//      }
//      isWaitingFor.foreach(A => if (A._2 contains node) {println("transitive waiting: " + A._1 + " is also waiting for " + reason); addReason(A._1,reason)})
//      println("isWaitingFor: " + isWaitingFor.get(node))
      if (isWaitingFor.get(node).exists(n => n contains node)) {
//        println("there is a conflict")
        removeReplacement(isWaitingFor(node))
      }
    }
    
    def removeReplacement(cycle: MSet[SequentProofNode]) {
//      println("cycle:")
//      cycle.foreach(println)
//      println("replacements: " + replaceNodes.size)
//      replaceNodes.foreach(println)
      val remove = replaceNodes.find(A => cycle contains A._1).map(A => A._1)
      remove match {
        case None => //println("no replacement has to be replaced node as first element in cycle")
        case Some(rep) => {
          replaceNodes -= rep
//          println("replacements: " + replaceNodes.size)
//          replaceNodes.foreach(println)
//          jumpTo(remove)
        }
      }
      
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
      
//    proof bottomUp collect
//    println("replaceNodes after collect:")
//    replaceNodes.foreach(println)
//    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      if (replaceNodes.isDefinedAt(node)) println("bla")
//      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
//    })})
    
    
    normalize()
//    replaceNodes.foreach(A => (println(A._1 + " <-- " + A._2)))
//    val outRoot = proof.foldDown2(replace)(replaced)
    val out = Proof(proof.foldDown3(replace2)(nextNode))
    println(out.root.conclusion.size == 1)
//    require (out.root.conclusion.isEmpty)
    out foldDown checkReplaced
//    println(out.root eq proof.root)
//    println(isWaitingFor contains out.root)
//    println(replaced.size)
//    isWaitingFor.foreach(println)
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
