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
    var replacedChild:SequentProofNode = null
    val resulted = new MSet[SequentProofNode]
    val resultedPremises = new MSet[SequentProofNode]
    val visited = new MSet[SequentProofNode]
    
    val allreplacednodes = new MSet[SequentProofNode]
    val alloutnodes = new MSet[SequentProofNode]
     //(382,383,417,418,419,442,443,444,521,522,523,525,526,538,543,544,545,546,547,548)
    //1107
    val checkThisOut = Array[Int](1732)
    
    def printInfo(node: SequentProofNode) {
       println(node.conclusion + " #" +visitNumber.getOrElse(node, "no visit#") + " replaced?: " + (replaced contains node) + " " + node.hashCode())
     }
    
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

    def oldReplace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (replaceNodes.isDefinedAt(node)) {
        val replacement = replaceNodes(node)
        println(Proof(replacement).size + " replaces <replace> " + Proof(node).size)
        //println(replacement.conclusion + " replaces <replace> " + node.conclusion)
      }
      val n = replaceNodes.get(node) match {
        case Some(u) => {
          replaced += node
          u
        }
        case None => {
          val newNode = node match {
            case R(left, right, pivot, _) => {
              if (fixedPremises.isEmpty) node
              else {
                val fixedLeft  = fixedPremises.head
                val fixedRight = fixedPremises.last
                if ((left eq fixedLeft) && (right eq fixedRight)) node 
                else {
                   val l = if (left eq fixedLeft) left else fixedLeft
                   val r = if (right eq fixedRight) right else fixedRight
                   R(l,r,pivot,true)
                }
              }
            }
            case _ => node
          }

          newNode
        }
      }

      for ((n1,n2) <- replaceNodes) {
        if (n2 eq n) replaceNodes(n1) = n
      }
      
      for (p <- n.premises if replaced contains p) println("this shouldn't happen!") // and it is not happening
      
      if (replaced contains n) println("this also shouldn't happen!") // and it is not happening
      
      // since the two bad things above are not happening, 
      // it seems that calls to replace are not returning anything that should have been replaced.
      
      // Let's test this hypothesis once again by tracking everything (nodes and their premises) that is returned by calls to replace
      resulted += n
      for (p <- n.premises) resultedPremises += p
      
      n
    }

    var goodRoot:SequentProofNode = null
    var rootFound = false
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      counter = counter + 1
      
      visitNumber += (node -> counter)
      val newNode = fixNode(node,fixedPremises.map(f => deepReplace(f)))
      for ((n1,n2) <- replaceNodes) {
        if (n2 eq node) replaceNodes(n1) = deepReplace(newNode)
      }
      var replaceNode:SequentProofNode = deepReplace(newNode)
      replaceNode = fixNode(replaceNode,replaceNode.premises)
      if (!(replaceNode eq node)) {counter = counter + 1; visitNumber += (replaceNode -> counter); replaceNodes(node) = replaceNode; replaced += node}
      if (counter == checkThisOut(0)){
        oneNewNode = replaceNode
         print("OLD\n")
         printInfo(node)
         println("NEW")
         printInfo(replaceNode)
         println("NEW premises")
         (replaceNode.premises).foreach(c => printInfo(c))
         println("OLD premises")
         (node.premises).foreach(c => printInfo(c))
      }
      if (replacedChild != null) {
//        println("juptidu")
        if (replacedChild eq node) {
          println("***************************")
          print("This is the replaced Child\n")
          printInfo(node)
           println("it's fixed premises")
           (fixedPremises).foreach(c => printInfo(c))
           println("***************************")
        }
      }
      oldvsnew += (replaceNode -> node)
      allreplacednodes += replaceNode
      //if ((node.conclusion subsequentOf replaceNode.conclusion) && (replaceNode.conclusion subsequentOf node.conclusion)) node
      //else replaceNode
      if (rootFound) {
        println("root already found")
        println("node")
        printInfo(node)
        println("replaceNode")
        printInfo(replaceNode)
      }
      if (replaceNode.conclusion.size == 1) {
        println("*********root found********")
        printInfo(replaceNode)
        println(counter)
        println("***************************")
        rootFound = true
      }
      visited += node
      val notVisitedPremise = fixedPremises.find(p => !(visited contains p))
      notVisitedPremise.foreach(p => {goodRoot = replaceNode; println("this nodes premise has not yet been visited: "); printInfo(node); println("premise: ");printInfo(p);println( " not visited yet")})
      
      replaceNode
    }
    def premiseTest(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (fixedPremises.size == 2) {
        if (replaced contains fixedPremises.head) fixedPremises.last
        else if (replaced contains fixedPremises.last) fixedPremises.head
        else node
      }
      else node
    }
    
    def checkOutPremises(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (node eq oneNewNode) {
        print("replaced " + checkThisOut(0) + "  in out proof \n")
        printInfo(node)
        println("premises")
        node.premises.foreach(c => printInfo(c))
      }
      if (visitNumber.getOrElse(node, -1) == checkThisOut(0))
      {
        print("faulty " + checkThisOut(0) + " in out proof \n")
        printInfo(node)
        println("premises")
        node.premises.foreach(c => printInfo(c))
      }
      node
    }
    var interestingChild:SequentProofNode = null
    def checkOutChildren(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      if (node eq oneNewNode) {
        print("replaced " + checkThisOut(0) + " in out proof \n")
        printInfo(node)
        println("children")
        children.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
      }
      if (visitNumber.getOrElse(node, -1) == checkThisOut(0))
      {
        print("faulty " + checkThisOut(0) + " in out proof \n")
        printInfo(node)
        println("children")
        children.foreach(c => {interestingChild = c; printInfo(c)})
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
        println("replaced node still occurs")
        printInfo(node)
        println("its children: ")
        children.foreach(c => printInfo(c))
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
     
     var isFirstOne = true
     var firstReplaced = true

     def childOfReplaced(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
       if (!((replaced intersect children.toSet).isEmpty) && firstReplaced) {
         print("This node has a replaced child\n")
         printInfo(node)
         println("replaced children")
         (replaced intersect children.toSet).foreach(c => {
           printInfo(c)
           replacedChild = c
         })
         firstReplaced = false
         
       }
       node
     }
     
     def premiseRepl(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
       if (!((replaced intersect fixedPremises.toSet).isEmpty) && !(replaced contains node)) {
         print("This node is not replaced while one of its premises is\n")
         printInfo(node)
         println("replaced premises")
         (replaced intersect fixedPremises.toSet).foreach(c =>  printInfo(c))
       }
       node
     }
     
     def childOfNotVisited(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
       val badpremises = if (visitNumber.isDefinedAt(node)) fixedPremises.filter(p => !(visitNumber.isDefinedAt(p))) else MSet()
       if (!(badpremises).isEmpty && isFirstOne) {
           print("This node non visited child\n")
           printInfo(node)
           println("non visited child")
           (badpremises).foreach(c => printInfo(c))
           println("all childs")
           (node.premises).foreach(c => printInfo(c))
           isFirstOne = false
           
       }
       node
     }
     
     def emptyNode(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
       if (node.conclusion.size == 1) {
         print("root\n")
         printInfo(node)
       }
       node
     }
     var getCheckOutNode:SequentProofNode = null
     def getCheckOut(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
       if (visitNumber.getOrElse(node, -1) == checkThisOut(0)){
         getCheckOutNode = node
       }
       node
     }
     
     
    val proof = setTraverseOrder(inputproof)
    print("\n")
    proof bottomUp collect
//    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      if (replaceNodes.isDefinedAt(node)) println("bla")
//      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
//    })})
//    println("\nat first: " + replaceNodes.size)
//    val out1 = Proof(proof foldDown replace)
//    println(proof.size)
//    println(replaced.size)
//    println("then " + replaceNodes.size)
    val out = Proof(proof foldDown replace)
//    println("then " + replaceNodes.size)
//    val out2 = Proof(proof foldDown replace)
//    val out3 = Proof(out2 foldDown replace)
    
//    println((changed.map(n => n.conclusion) intersect replaced.map(n => n.conclusion)).isEmpty)
    
//    val out2 = Proof(out foldDown fixAll)
//    println("---")
//    out bottomUp childOfNotVisited
//    out bottomUp emptyNode
//    println(goodRoot eq out.root)
//    println("Is a node that should have been replace still reachable from the root of output proof? : " + out.root.existsAmongAncestors(n => replaced contains n))
    print("out root\n")
    printInfo(out.root)
//    out foldDown getCheckOut
    visitNumber.foreach(N => {if (N._2 == 1732) getCheckOutNode = N._1})
    printInfo(getCheckOutNode)
//    println("root premises")
//    (out.root.premises).foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
//    out bottomUp childOfReplaced
//    val out1 = Proof(proof foldDown premiseTest)
//      out foldDown checkReplaced
//      out bottomUp checkVisit2
//      out foldDown checkOutPremises
//      out foldDown premiseRepl
//      out bottomUp checkOutChildren
//      out bottomUp checkOutInterestingChild
//      println("premises")
//      interestingChild.premises.foreach(c => println(c.conclusion+ " #" +visitNumber.getOrElse(c, "no visit#")+ " " + c.hashCode()))
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
    getCheckOutNode
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
