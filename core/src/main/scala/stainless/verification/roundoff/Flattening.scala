/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
package roundoff

import trees._

/** One floating-point value a function was given, named by the way it is reached.
  *
  * A bare parameter has no fields; `s.cal.offset` has two. Two readings of the same path are the
  * same value, which is what makes flattening sound: the analysis may not treat them as free of
  * each other.
  */
case class FieldPath(root: Variable, fields: Seq[Identifier]) {
  def name: String = (root.id.name +: fields.map(_.name)).mkString("_")

  /** The expression this path stands for, rebuilt. */
  def expr: Expr = fields.foldLeft(root: Expr)(ADTSelector(_, _))

  /** The objects passed through on the way, the outermost first, ending before the value. */
  def objects: Seq[Expr] =
    fields.inits.toSeq.drop(1).reverse.map(fs => fs.foldLeft(root: Expr)(ADTSelector(_, _)))
}

/** What the fields a function reads became, once each of them is a value of its own.
  *
  * The rest of the analysis only ever sees variables, which is the point: a field of a parameter
  * carries exactly what a parameter carries, so it is made into one rather than taught about
  * everywhere.
  */
case class Flattening(scalars: Map[FieldPath, Variable], parameters: Seq[ValDef]) {

  /** The same reading of a field, wherever else it appears.
    *
    * Used on a precondition and on a class invariant, which speak of the fields the body reads but
    * were written before it was rewritten. A field the body never reads is left as it was, since
    * nothing will be asked about it.
    */
  def substitute(e: Expr)(using Symbols): Expr = Flattening.rewrite(e, scalars.get)

  /** The objects every path passes through, each of which may carry an invariant of its own. */
  def objects: Seq[Expr] = scalars.keys.flatMap(_.objects).toSeq.distinct
}

object Flattening {

  /** Reads every floating-point field the body reaches as a value of its own.
    *
    * A path has to bottom out in a parameter. Inlining binds a callee's arguments rather than
    * substituting them, so a helper reads `p'.x` where the caller wrote `p.x`; those are followed
    * back to the same path, since making them two values would let the analysis believe they can
    * differ.
    */
  def of(fd: FunDef, body: Expr)(using Symbols): Either[String, (Expr, Flattening)] = {
    val given_ = fd.params.map(p => p.id -> p.toVariable).toMap
    val minted = scala.collection.mutable.LinkedHashMap.empty[FieldPath, Variable]

    def scalar(path: FieldPath, tpe: Type): Variable =
      minted.getOrElseUpdate(path, Variable.fresh(path.name, tpe))

    def rec(e: Expr, aliases: Map[Identifier, FieldPath]): Either[String, Expr] = e match {
      case selector @ ADTSelector(_, _) if isValue(selector.getType) =>
        pathOf(selector, aliases) match {
          case Some(path) if given_.contains(path.root.id) =>
            Right(scalar(path, selector.getType))
          case Some(path) =>
            Left(s"'${path.name}' is read off '${path.root.id.name}', which is not one of the " +
              s"values '${fd.id.name}' was given")
          case None =>
            Left("a field is read off something the analysis cannot follow back to a parameter")
        }

      case Let(vd, value, body) =>
        // A binding of one object to another is followed rather than kept, so that a field read
        // through it is the same value as the one read directly.
        val inner = pathOf(value, aliases).fold(aliases)(path => aliases + (vd.id -> path))

        for { bound <- rec(value, aliases); rest <- rec(body, inner) } yield
          // The scaffolding that passed the object around has nothing left reading it.
          if (isValue(vd.tpe) || exprOps.variablesOf(rest).exists(_.id == vd.id))
            Let(vd, bound, rest)
          else rest

      case Operator(operands, build) => traverse(operands)(rec(_, aliases)).map(build)
    }

    rec(body, Map.empty).map { flattened =>
      val scalars = minted.toMap
      val parameters = fd.params.flatMap { p =>
        if (isValue(p.tpe)) Seq(p)
        else minted.collect { case (path, v) if path.root.id == p.id => (path.name, v.toVal) }
               .toSeq.sortBy(_._1).map(_._2)
      }
      (flattened, Flattening(scalars, parameters))
    }
  }

  /** Where an expression is read from, where that is a value the function was given. */
  private def pathOf(e: Expr, aliases: Map[Identifier, FieldPath]): Option[FieldPath] = e match {
    case v: Variable => Some(aliases.getOrElse(v.id, FieldPath(v, Seq.empty)))
    case ADTSelector(receiver, field) =>
      pathOf(receiver, aliases).map(path => FieldPath(path.root, path.fields :+ field))
    case _ => None
  }

  /** Replaces the readings `known` has a value for, and leaves the rest as they were. */
  private def rewrite(e: Expr, known: FieldPath => Option[Variable])(using Symbols): Expr = {
    def rec(e: Expr, aliases: Map[Identifier, FieldPath]): Expr = e match {
      case selector @ ADTSelector(_, _) =>
        pathOf(selector, aliases).flatMap(known).getOrElse {
          val ADTSelector(receiver, field) = selector: @unchecked
          ADTSelector(rec(receiver, aliases), field)
        }

      case Let(vd, value, body) =>
        val inner = pathOf(value, aliases).fold(aliases)(path => aliases + (vd.id -> path))
        Let(vd, rec(value, aliases), rec(body, inner))

      case Operator(operands, build) => build(operands.map(rec(_, aliases)))
    }

    rec(e, Map.empty)
  }

  private def isValue(tpe: Type): Boolean = tpe match {
    case FPType(_, _) => true
    case _ => false
  }
}
