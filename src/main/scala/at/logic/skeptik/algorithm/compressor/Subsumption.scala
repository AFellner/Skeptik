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
    val nodes = new MSet[SequentProofNode]
    val replaced = new MSet[SequentProofNode]
    val visitNumber = new MMap[SequentProofNode,Int]
    val replaced1 = new MSet[SequentProofNode]
    val changed = new MSet[SequentProofNode]
    val oldvsnew = new MMap[SequentProofNode,SequentProofNode]
    var counter = 0
    var n928:SequentProofNode = null
    var n929:SequentProofNode = null
    var i = 0
    var oneNewNode:SequentProofNode = null
    
    
    val allreplacednodes = new MSet[SequentProofNode]
    val alloutnodes = new MSet[SequentProofNode]
     //(382,383,417,418,419,442,443,444,521,522,523,525,526,538,543,544,545,546,547,548)
    //1107
    val checkThisOut = Array[Int](1465)
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val subsumer = nodes.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumer match {
        case None => nodes += node
        case Some(u) => {
//          println(u + " replaces <collect> " + node)
          replaceNodes(node) = u
        }
      }
    }
  
    def deepReplace(node: SequentProofNode):SequentProofNode = {
      var outNode = node
      while(replaceNodes.isDefinedAt(outNode)) {
        outNode = replaceNodes(outNode)
      }
      
      outNode
    }
    
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      counter = counter + 1
//      if (node.premises contains n929) {
//        println("929 is premis before")
//      }
//      if (counter == 928) {
//        println("#928: " + node.conclusion)
////        println("replace? : "+ replaceNodes.isDefinedAt(node))
//        println("replace with: " + replaceNodes(node).conclusion)// +  " #" + visitNumber(replaceNodes(node)))
//      }
//      if (counter == 929)
//      {
//        n929 = node
//        println("#929 "+node.conclusion)
//        println("premises")
//        node.premises.foreach(p => println(p.conclusion))
//        println("fixedPremises")
//        fixedPremises.foreach(p => println(p.conclusion))
//      }
//      if (counter == 930)
//      {
//        println("#930 " + node.conclusion)
//        println("contains 929 as premise: " + (node.premises contains n929))
//        println("premises")
//        node.premises.foreach(p => println(p.conclusion))
//        println("fixedPremises")
//        fixedPremises.foreach(p => println(p.conclusion))
//      }
      visitNumber += (node -> counter)
      if (replaceNodes.isDefinedAt(node)) {
        val replacement = replaceNodes(node)
        //println(Proof(replacement).size + " replaces <replace> " + Proof(node).size)
//        println(replacement.conclusion + " replaces <replace> \n" + node.conclusion)
      }
      val newNode = fixNode(node,fixedPremises)
      for ((n1,n2) <- replaceNodes) {
        if (n2 eq node) replaceNodes(n1) = deepReplace(newNode)
      }
//      deepReplace(newNode)
      var replaceNode:SequentProofNode = deepReplace(newNode)
      if (!(replaceNode eq node)) replaced += node
//      replaceNodes.get(newNode) match {
//        case Some(u) => {
//          if (counter == 928) n928 = u
//          if (counter == 929) println("929 goes to replace")
//          replaced += node
//          replaceNode = u
//        }
//        case None => {
//          if (counter == 929) println("929 goes to fix")
//          if (counter == 928) n928 = newNode
//          
//          
//          if (!(node eq newNode)) changed += newNode
//          val replacedStillPremise = (replaced intersect node.premises.toSet)
////          if (!(replacedStillPremise.isEmpty)) {
////            println("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")
////            println("node has replaced node as premise " + node.conclusion + " ~ " + node.hashCode() + " ~ " + (replaceNodes.isDefinedAt(newNode)))
////            println("newNode: " + newNode.conclusion)
////            
////            replacedStillPremise.foreach(p => println("premises visit # : " + visitNumber(p)))
////            println("visit # of node: " + visitNumber(node))
//////            println("premises contains replaced node: " + (!((replaced intersect node.premises.toSet).isEmpty)))
//////            println("fixedPremises contains replaced node: " + (!((replaced intersect fixedPremises.toSet).isEmpty)))
////            println("newNode's premises contains replaced node: " + (!((replaced intersect newNode.premises.toSet).isEmpty)))
////          }
////          if (replaceNodes.isDefinedAt(newNode)) {
////            println("asdsifasdasd")
////            replaceNodes(newNode)
////          }
////          else {
//            if (counter == 929) println("929 fixed to " + newNode.conclusion)
//            if (counter == 929) println("929 fixed to 928? " + (newNode eq n928))
//            if (counter == 929) println(newNode.conclusion)
//            if (counter == 929) println(n928.conclusion)
//            replaceNode = newNode
////          }
//        }
//      }
//      if (node.premises contains n929) {
//        println("929 in premises afterwards: " + (replaceNode.premises contains n929))
//      }
//      if (counter == 930) {
//        println("930 afterwards: " + replaceNode.conclusion)
//        println("contains 929 as premise: " + (replaceNode.premises contains n929))
//        println("fixedPremises")
//        replaceNode.premises.foreach(p => println(p.conclusion))
//      }
      if (checkThisOut contains counter){
        print("--------------\n")
        println(counter + " before \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        //println("should be:\n"  + R(node.premises.head,node.premises.last).conclusion)
//        println("fixed premises")
//        fixedPremises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#") + c.hashCode()))
        println("after\n"+replaceNode.conclusion + " #" + visitNumber.getOrElse(replaceNode, "no visit#") + " " + replaceNode.hashCode())
        println("premises")
        node.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
        println("new premises")
        replaceNode.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
        print("--------------\n")
      }
      if (counter == checkThisOut(0)){
        oneNewNode = replaceNode
      }
      oldvsnew += (replaceNode -> node)
      allreplacednodes += replaceNode
      //if ((node.conclusion subsequentOf replaceNode.conclusion) && (replaceNode.conclusion subsequentOf node.conclusion)) node
      //else replaceNode
      replaceNode
    }
    
    def getOutNodes(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      alloutnodes += node
      node
    }
    
    def soundCheck(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      
      if (!(oldvsnew.isDefinedAt(node))) {
        println("this should not happen")
        i = i +1
      }
      
      node
    }
    
    def checkOutPremises(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (node eq oneNewNode) {
        print("--------------\n")
        println("replaced " + checkThisOut(0) + "  in out proof \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        println("premises")
        node.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      if (visitNumber.getOrElse(node, -1) == checkThisOut(0))
      {
        print("--------------\n")
        println("faulty " + checkThisOut(0) + " in out proof \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        println("premises")
        node.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      node
    }
    var interestingChild:SequentProofNode = null
    def checkOutChildren(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      if (node eq oneNewNode) {
        print("--------------\n")
        println("replaced " + checkThisOut(0) + " in out proof \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        println("children")
        children.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      if (visitNumber.getOrElse(node, -1) == checkThisOut(0))
      {
        print("--------------\n")
        println("faulty " + checkThisOut(0) + " in out proof \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        println("children")
        children.foreach(c => {interestingChild = c; println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode())})
      }
      node
    }
    
    def checkOutInterestingChild(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      if (node eq interestingChild) {
        print("INTERESTING\n")
        println("intertesting child:  in out proof \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#")+ " " + node.hashCode())
        println("children")
        children.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      node
    }
    
    def checkVisit2(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
     
      if (visitNumber.isDefinedAt(node)) {
        var number = visitNumber(node)
       
        if (checkThisOut contains number){
          println("children of " + number)
          children.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#") + " " + c.hashCode()))
        }
      }
      node
    }
    
    
    def checkReplaced(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      if (replaced contains node) {
        replaced1 += node
        println("replaced node still occurs \n" + node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#"))
        println("its children: ")
        children.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      node
    }
    
     def checkReplaced1(node: SequentProofNode, fixedPremises: Seq[Unit]):Unit = {
       if (replaced1 contains node) {
         println("original proof contains: \n" + node.conclusion)
       }
     }
     
     def displayNumbers(node: SequentProofNode, fixedPremises: Seq[Unit]):Unit = {
       println(" #" +visitNumber.getOrElse(node, "no visit#") + " " + node.hashCode())
     }
     
     def checkReplaced2(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      val replacedStillPremise = (replaced intersect node.premises.toSet)
      if (!(replacedStillPremise.isEmpty)) {
        replaced1 += node
        println("node has replaced node as premise " + node.conclusion + " ~ " + node.hashCode())
       
        replacedStillPremise.foreach(p => println("premises visit # : " + visitNumber(p)))
        println("visit # of node: " + visitNumber(node))
//        println("node's class: " + node.getClass())
//        println("fixNode: " + fixNode(node,fixedPremises).conclusion)
//        println("fixedPremises contain this node: " + (!((replaced intersect fixedPremises.toSet).isEmpty)))
//        println("its premises: ")
//        node.premises.foreach(c => println(c.conclusion))
      }
      node
    }
     
     def fixAll(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
       fixNode(node,fixedPremises)
     }
    val proof = setTraverseOrder(inputproof)

    proof bottomUp collect
//    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      if (replaceNodes.isDefinedAt(node)) println("bla")
//      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
//    })})
    val out = Proof(proof foldDown replace)
//    val out2 = Proof(out foldDown replace)
//    val out3 = Proof(out2 foldDown replace)
    
//    println((changed.map(n => n.conclusion) intersect replaced.map(n => n.conclusion)).isEmpty)
    
//    val out2 = Proof(out foldDown fixAll)
//    println("---")
//      out foldDown checkReplaced
//      out bottomUp checkVisit2
      out foldDown checkOutPremises
      out bottomUp checkOutChildren
      out bottomUp checkOutInterestingChild
      println("premises")
      interestingChild.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
//      out bottomUp soundCheck
//      println("but it happens " + i + " times")
//      println((proof.root.hashCode()) == out.root.hashCode())
      //out foldDown displayNumbers
//      out foldDown checkVisit
//    println("---")
//    inputproof foldDown checkReplaced2
//    println("---")
//      for (i <- 0 to alloutnodes.size-1) {
//        if (alloutnodes)
//      }
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
