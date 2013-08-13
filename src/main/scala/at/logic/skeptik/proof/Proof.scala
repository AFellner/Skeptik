package at.logic.skeptik.proof

import language.implicitConversions

import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}
import annotation.tailrec

import at.logic.skeptik.judgment.Judgment

// ProofNode tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
class Proof[P <: ProofNode[Judgment,P]](val root: P, val leftRight: Boolean)
extends Iterable[P]
{
  def this(root: P) = this(root,true)
  
  def initialize() = {
    val nodes = Stack[P]()
    val children = MMap[P,IndexedSeq[P]](root -> IndexedSeq())
    val visited = MSet[P]()
    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      val pr = if (leftRight) p.premises else p.premises.reverse
      pr.foreach(premise => {
        visit(premise)
        children(premise) = p +: children.getOrElse(premise,IndexedSeq())
      })
      nodes.push(p)
    }
    visit(root)
    (nodes.toIndexedSeq, children.toMap)
  }
  
  val (nodes, childrenOf) = initialize()
    
  override def iterator:Iterator[P] = nodes.iterator
  override def isEmpty:Boolean = nodes.isEmpty
  override lazy val size:Int = nodes.length // ToDo: nodes is IndexedSeq, and nodes.length should take constant time. Therefore it might be ok to make this a def instead of a val


  def foldDown[X](f: (P, Seq[X]) => X): X = {
    val resultFrom = MMap[P,X]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val node = nodes(pos)
      resultFrom(node) = f(node, node.premises.map(resultFrom)) // TODO: remove "toList"
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(0))
  }
  

  def foldDown3[X](f: (P, Seq[X]) => X)(nextNode: Next[X]): X = {
    val resultFrom = MMap[P,X]()
    @tailrec def iterate(pos:Int):Unit = {
      println(nextNode.hashCode())
      if (pos < 0) return
      val node = nodes(pos)
      resultFrom(node) = f(node, node.premises.map(resultFrom)) // TODO: remove "toList"
      nextNode.next match {
        case None => iterate(pos-1)
        case Some(nn) => iterate(
            if (nodes contains nn) {
//              println("go somewhere else")
              nodes.indexOf(nn)
            }
            else {
//              println("index not defined")
              pos-1
            }
            )
      }
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(0))
  }
  
  type N = at.logic.skeptik.proof.sequent.SequentProofNode
  def foldDown2(f: (N, Seq[N]) => N)(badNodes: collection.mutable.HashSet[N]): N = {
    val resultFrom = MMap[N,N]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val node: N = nodes(pos).asInstanceOf[N]
      val nNode = f(node, node.premises.map(resultFrom))
      if (badNodes contains nNode) println("! shouldn't happen") // and is not happening
      for (p <- nNode.premises if badNodes contains p) println("! shouldn't happen") //and is not happening
      if (nNode.existsAmongAncestors(n => badNodes.contains(n))) {
        println("!! shouldn't happen") // and it is happening!
        println(nNode.hashCode())
        println(nNode.conclusion)
        for (b <- badNodes if nNode.existsAmongAncestors(n => n eq b)) println("This bad node occurs among ancestors: " + b.hashCode())
      }
      resultFrom(node) = nNode
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    println(nodes(0).asInstanceOf[N].hashCode())
    val r = resultFrom(nodes(0).asInstanceOf[N])
    if (r.existsAmongAncestors(n => badNodes.contains(n))) {
      println("Root: shouldn't happen") // and it is happening!
      println(r.hashCode())
      println(r.conclusion) 
    }
    if (r.conclusion.isEmpty) println("empty: " + r.hashCode())
    r
  }

  def bottomUp[X](f:(P, Seq[X])=>X):Unit = {
    val resultsFromChildren = MMap[P, Seq[X]]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos >= size) return
      val node = nodes(pos)
      val result = f(node, resultsFromChildren.getOrElse(node,Nil))
      resultsFromChildren -= node
      node.premises.foreach(premise => resultsFromChildren(premise) = (result +: resultsFromChildren.getOrElse(premise, Seq())))
      iterate(pos + 1)
    }
    iterate(0)
  }

  override def toString = {
    var counter = 0; var result = "";
    foldDown { (n:P, r:Seq[Int]) =>
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t: " +
                n.name + "(" + r.mkString(", ") + ")[" + n.parameters.mkString(", ") + "]" + " ~ " + n.hashCode() + "\n"
      counter
    }
    result
  }
}

class Next[X]() {
  var next:Option[X] = None
}

object Proof {
  implicit def apply[P <: ProofNode[Judgment,P]](root: P) = new Proof(root)
}