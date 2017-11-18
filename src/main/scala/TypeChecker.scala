
/**
  * Created by Anindo Saha on 10/23/17.
  */
object TypeChecker {
  sealed trait Exp
  case class Var(id: String) extends Exp
  case class Num(n: Int) extends Exp
  case class Bool(b: Boolean) extends Exp
  case class Lambda(binder: String, body: Exp) extends Exp
  case class Application(left: Exp, right: Exp) extends Exp
  case class Conditional(cond: Exp, conseq: Exp, alter: Exp) extends Exp
  case class Let(st: Stmt, body: Exp) extends Exp

  sealed trait Stmt
  case class Empty() extends Stmt
  case class Assign(lhs: String, rhs: Exp) extends Stmt
  case class Seq(left: Stmt, right: Stmt) extends Stmt

  sealed trait Type
  case class IntType() extends Type
  case class BoolType() extends Type
  case class VarType(id: String) extends Type
  case class ArrowType(src: Type, dst: Type) extends Type

  type Constraint = (Type, Type)
  type Substitution = Map[VarType, Type]

  sealed trait UnificationError
  case object CyclicError extends UnificationError
  case object UnificationError extends UnificationError

  /*
    type binding =
      NameBind
    | VarBind of ty
  */
  sealed trait Binding
  case class NameBind() extends Binding
  case class VarBind(t: Type) extends Binding

  // type context = (string * binding) list
  case class Gamma(bindings: Map[String, Binding])

  // let addbinding ctx x bind = (x,bind)::ctx
  def addBinding(gamma: Gamma, vari: String, binding: Binding): Gamma = {
    Gamma(gamma.bindings + (vari -> binding))
  }

  // val getbinding : info → context → int → binding
  def getBinding(gamma: Gamma, vari: String): Binding = {
    gamma.bindings.get(vari) match {
      case Some(binding) => binding
      case _ => null
    }
  }

  /*
    let getTypeFromContext fi ctx i =
    match getbinding fi ctx i with
      VarBind(tyT) → tyT
    | _ → error fi
      ("getTypeFromContext: Wrong kind of binding for variable "
        ^ (index2name fi ctx i))
  */
  def getTypeFromContext(gamma: Gamma, vari: String): Option[Type] = {
    getBinding(gamma, vari) match {
      case VarBind(t) => Some(t)
      case _ => None
    }
  }

  def rewriteType(x: String, replaceWith: Type, inside: Type): Type = {
    inside match {
      case VarType(x_) => if (x == x_) replaceWith else VarType(x_)
      case ArrowType(from, to) => ArrowType(rewriteType(x, replaceWith, from), rewriteType(x, replaceWith, to))
      case other => other
    }
  }

  def rewriteConstraints(x: String, typ: Type, constraints: List[Constraint]): List[Constraint] = {
    constraints.map {
      case (l, r) =>
        (rewriteType(x, typ, l), rewriteType(x, typ, r))
    }
  }

  def conflicts(variable: String, typ: Type): Boolean = {
    typ match {
      case VarType(x) => variable == x
      case ArrowType(from, to) =>
        conflicts(variable, from) || conflicts(variable, to)
      case IntType() | BoolType() => false
    }
  }

  /**
    * Task 2
    *
    * @param constraints
    * @return Substitution
    */
  def unify(constraints: List[Constraint]): Either[UnificationError, Substitution] = {
    constraints match {
      case Nil => Right(Map())
      case (VarType(x), r) :: rest => {
        val fst = (VarType(x), r)
        if (VarType(x) == r)
          unify(rest)
        else if (conflicts(x, r)) {
          Left(CyclicError)
        }
        else {
          unify(rewriteConstraints(x, r, rest)) match {
            case Left(error) => Left(error)
            case Right(x) => Right(x ++ Map(fst))
          }
        }
      }
      case (l, VarType(x)) :: rest => {
        val fst = (VarType(x), l)
        if (l == VarType(x))
          unify(rest)
        else if (conflicts(x, l)) {
          Left(CyclicError)
        }
        else {
          unify(rewriteConstraints(x, l, rest)) match {
            case Left(error) => Left(error)
            case Right(x) => Right(x ++ Map(fst))
          }
        }
      }
      case (IntType(), IntType()) :: rest => unify(rest)
      case (BoolType(), BoolType()) :: rest => unify(rest)
      case (ArrowType(from1, to1), ArrowType(from2, to2)) :: rest => {
        // A -> B = C -> D
        // A = C, B = D
        unify(List((from1, from2), (to1, to2)) ++ rest)
      }
      case (_, _) :: _ => Left(UnificationError)
    }
  }

  object generateVarType {
    var init: Int = 0

    def apply(): VarType = {
      init += 1
      VarType("var_" + init)
    }
  }

  def tests(): Unit = {
    // Some(BoolType())
    val htest1 = Application(Application(Lambda("x", Lambda("y", Var("y"))), Num(1)), Bool(true))
    val hres1: Option[Type] = typeCheck(htest1)

    // Some(IntType())
    val htest2 = Conditional(Application(Lambda("x", Var("x")), Bool(true)), Num(1), Num(2))
    val hres2: Option[Type] = typeCheck(htest2)

    // None
    val htest3 = Conditional(Bool(true), Conditional(Bool(false), Num(1), Num(2)), Bool(false))
    val hres3: Option[Type] = typeCheck(htest3)

    // None
    val htest4 = Let(Assign("x", Num(2)), Application(Var("x"), Num(3)))
    val hres4: Option[Type] = typeCheck(htest4)

    // Some(BoolType())
    val htest5 = Bool(true)
    val hres5: Option[Type] = typeCheck(htest5)

    // None
    val htest6 = Lambda("x", Var("x"))
    val hres6: Option[Type] = typeCheck(htest6)

    // None
    val htest7 = Application(Num(0), Bool(true))
    val hres7: Option[Type] = typeCheck(htest7)

    // Some(IntType())
    val htest8 = Application(Lambda("x", Var("x")), Num(0))
    val hres8: Option[Type] = typeCheck(htest8)

    // Some(IntType())
    val htest9 = Conditional(Bool(true), Num(0), Num(2))
    val hres9: Option[Type] = typeCheck(htest9)

    // None
    val htest10 = Conditional(Num(0), Num(0), Num(2))
    val hres10: Option[Type] = typeCheck(htest10)

    // Some(IntType())
    val htest11 = Application(Lambda("x", Num(2)), Bool(true))
    val hres11: Option[Type] = typeCheck(htest11)

    // Some(IntType())
    val htest12 = Application(Lambda("x", Application(Var("x"), Num(2))), Lambda("y", Var("y")))
    val hres12: Option[Type] = typeCheck(htest12)

    // None
    val htest13 = Lambda("x", Conditional(Var("x"), Num(1), Bool(true)))
    val hres13: Option[Type] = typeCheck(htest13)

    // Some(ArrowType(BoolType(),IntType()))
    val htest14 = Lambda("x", Conditional(Var("x"), Num(1), Num(2)))
    val hres14: Option[Type] = typeCheck(htest14)

    // Some(ArrowType(BoolType(),IntType()))
    val htest15 = Let(Seq(Assign("a", Num(1)), Assign("b", Num(2))), Lambda("x", Conditional(Var("x"), Var("a"), Var("b"))))
    val hres15: Option[Type] = typeCheck(htest15)

    // None
    val htest16 = Let(Seq(Assign("a", Num(1)), Assign("b", Bool(false))), Lambda("x", Conditional(Var("x"), Var("a"), Var("b"))))
    val hres16: Option[Type] = typeCheck(htest16)

    // None
    val htest17 = Lambda("x", Num(2))
    val hres17: Option[Type] = typeCheck(htest17)

    // None
    val htest18 = Application(Lambda("x", Application(Var("x"), Var("x"))), Lambda("x", Application(Var("x"), Var("x"))))
    val hres18: Option[Type] = typeCheck(htest18)

    // None
    val htest19 = Lambda("x", Var("x"))
    val hres19: Option[Type] = typeCheck(htest19)

    // None
    val htest20 = Conditional(Var("x"), Var("y"), Application(Lambda("x", Var("x")), Var("y")))
    val hres20: Option[Type] = typeCheck(htest20)

    // None
    val htest21 = Application(Lambda("x", Var("x")), Application(Lambda("x", Var("x")), Application(Lambda("x", Var("x")), Application(Lambda("x", Var("x")), Var("x")))))
    val hres21: Option[Type] = typeCheck(htest21)

    // None
    val htest22 = Conditional(Var("x"), Application(Var("x"), Num(1)), Application(Var("x"), Num(2)))
    val hres22: Option[Type] = typeCheck(htest22)

    // None
    val htest23 = Application(Application(Lambda("x", Lambda("x", Application(Var("x"), Num(1)))), Lambda("y", Var("y"))), Num(2))
    val hres23: Option[Type] = typeCheck(htest23)

    // Some(IntType())
    val htest24 = Conditional(Conditional(Bool(true), Bool(false), Bool(true)), Num(5), Num(10))
    val hres24: Option[Type] = typeCheck(htest24)

    // Some(IntType())
    val htest25 = Application(Lambda("x", Var("x")), Num(3))
    val hres25: Option[Type] = typeCheck(htest25)

    // None
    val htest26 = Conditional(Conditional(Bool(true), Num(3), Num(5)), Var("y"), Num(2))
    val hres26: Option[Type] = typeCheck(htest26)

    // None
    val htest27 = Application(Lambda("y", Var("z")), Var("w"))
    val hres27: Option[Type] = typeCheck(htest27)

    // Some(IntType())
    val htest28 = Application(Application(Lambda("x", Lambda("b", Let(Seq(Assign("c", Var("b")), Assign("d", Var("c"))), Conditional(Var("d"), Var("x"), Num(4))))), Num(2)), Bool(true))
    val hres28: Option[Type] = typeCheck(htest28)

    // Some(IntType()) => TODO Need to debug
    val htest29 = Let(Seq(
      Assign("n", Num(2)),
      Assign("x", Lambda("y", Application(Var("y"), Bool(true))))),
      Application(Var("x"), Lambda("b", Conditional(Var("b"), Num(3), Var("n")))))
    val hres29: Option[Type] = typeCheck(htest29)

    // None
    val htest30 = Application(Lambda("x", Application(Var("x"), Var("x"))), Lambda("x", Application(Var("x"), Var("x"))))
    val hres30: Option[Type] = typeCheck(htest30)

    // None , mostly
    val htest31 = Let(Assign("x", Var("y")), Lambda("x", Application(Var("y"), Num(5))))
    val hres31: Option[Type] = typeCheck(htest31)

    // Some(IntType())
    val htest32 = Application(Application(Lambda("x", Lambda("y", Application(Var("y"), Var("x")))), Num(5)), Lambda("x0", Var("x0")))
    val hres32: Option[Type] = typeCheck(htest32)

    // None
    val htest33 = Application(Lambda("x", Application(Var("x"), Var("x"))), Lambda("y", Application(Var("y"), Var("y"))))
    val hres33: Option[Type] = typeCheck(htest33)

    // None
    val htest34 = Application(Conditional(Lambda("x", Var("x")), Num(1), Num(2)), Var("z"));
    val hres34: Option[Type] = typeCheck(htest34)

    // None
    val htest35 = Let(Assign("x", Var("y")), Var("x"))
    val hres35: Option[Type] = typeCheck(htest35)

    print()
  }

  def main(args: Array[String]): Unit = {

    tests();

    // Type Checks
    val X1 = Application(Lambda("x", Var("x")), Num(0))
    val type1: Option[Type] = typeCheck(X1)

    // Type Error
    val X2 = Lambda("x", Conditional(Num(10), Var("x"), Num(15)))
    val type2: Option[Type] = typeCheck(X2)

    // IS_ZERO
    // Type Checks
    val X3 = Lambda("n", Application(Var("n"), Application(Lambda("x", Bool(false)), Bool(true))))
    val type3: Option[Type] = typeCheck(X3)

    // Type Error
    val X4 = Application(Lambda("y", Conditional(Bool(true), Num(10), Var("y"))), Bool(false))
    val type4: Option[Type] = typeCheck(X4)

    println()
  }

  case class Box(constraints: List[Constraint], typ: Option[Type])

  /**
    * Generate constraints from the given expression.
    *
    * @param e
    * @return
    */
  def genConstraints(env: Gamma, e: Exp, constraints: List[Constraint]): Box = {
    e match {
      case Var(id) => {
        return Box(List(), getTypeFromContext(env, id))
      }
      // From Slide 6
      case Lambda(x, binder) => {
        val varType = generateVarType()
        val env_ = addBinding(env, x, VarBind(varType))
        val box: Box = genConstraints(env_, binder, constraints)
        box match {
          case Box(constraints_, Some(t)) => return Box(constraints_, Some(ArrowType(varType, t)))
          case Box(_, _) => return Box(constraints, None)
        }
      }
      case Application(e1, e2) => {
        val Box(constraint1, typ1) = genConstraints(env, e1, constraints)
        val Box(constraint2, typ2) = genConstraints(env, e2, constraints)
        val varType = generateVarType()
        (typ1, typ2) match {
          case (Some(t1), Some(t2)) => new Box(constraint1 ++ constraint2 ++ List((t1, new ArrowType(t2, varType))), Some(varType))
          case (_, _) => new Box(List(), None)
        }
      }
      case Num(_) => {
        /*return*/ Box(List(), Some(IntType()))
      }
      case Bool(_) => {
        /*return*/ Box(List(), Some(BoolType()))
      }
      case Conditional(cond: Exp, conseq: Exp, alter) =>
        val Box(constraint1, typ1) = genConstraints(env, cond, constraints)
        val Box(constraint2, typ2) = genConstraints(env, conseq, constraints)
        val Box(constraint3, typ3) = genConstraints(env, alter, constraints)
        (typ1, typ2, typ3) match {
          case (Some(t1), Some(t2), Some(t3)) =>
            new Box(constraint1 ++ constraint2 ++ constraint3
              ++ List((t1, BoolType()), (t2, t3)), Some(t2))
          case (_, _, _) => new Box(List(), None)
        }
      case Let(stmt, exp) => stmt match {
        case Empty() => genConstraints(env, exp, constraints)
        case Assign(lhs, rhs) => {
          // solve rhs
          val box = genConstraints(env, rhs, constraints)
          // assign to lhs
          box match {
            case Box(constraints_, Some(t)) => {
              val env_ = addBinding(env, lhs, VarBind(t))
              val exp_box = genConstraints(env_, exp, constraints_)
              exp_box match {
                case Box(constraints, Some(t)) => Box(constraints ++ constraints_, Some(t))
                case Box(_, _) => Box(List(), None)
              }
            }
            case _ => Box(List(), None)
          }
        }
        case Seq(left, right) => {
          genConstraints(env, Let(left, Let(right, exp)), constraints)
        }
      }
      case _ => new Box(List(), None)
    }
  }

  Some(BoolType())

  def solve(typ0: Type, substitution: Substitution): Option[Type] = {
    // pick one mapping and substitute in type
    substitution match {
      case s if s.isEmpty => {
        if (findVarType(typ0)) None else Some(typ0)
      }
      case _ =>
        Some(substitution.foldLeft(typ0) {
          case (typ, (VarType(x), r)) => {
            rewriteType(x, r, typ)
          }
        })

    }
  }

  def findVarType(typ0: Type): Boolean = {
    typ0 match {
      case VarType(x) => true
      case IntType() | BoolType() => false
      case ArrowType(from, to) => findVarType(from) || findVarType(to)
    }
  }

  /**
    * Task 3
    *
    * @param e
    * @return
    */
  def typeCheck(e: Exp): Option[Type] = {
    // Generate List[Constraint] and Type from an Exp
    var constraints = List()
    val box: Box = genConstraints(Gamma(Map()), e, constraints)
    // Use List[Constraint] to unify and create Substitution,
    box match {
      case Box(_, None) => None
      case Box(constraints, Some(t)) => {
        unify(constraints) match {
          case Left(_) => None
          // Use Substitution to compute the type of the Exp.
          case Right(substitution) => {
            val finalType = solve(t, substitution)
            finalType match {
              case None => None
              case Some(finalTyp) => if (findVarType(finalTyp)) None else Some(finalTyp)
            }
          }
        }
      }
    }
  }
}
