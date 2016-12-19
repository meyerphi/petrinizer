{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Property
    (Property(..),
     showPropertyName,
     renameProperty,
     PropertyType(..),
     PropertyContent(..),
     ConstraintProperty(..),
     Formula(..),
     Op(..),
     Term(..),
     PropResult(..),
     resultAnd,
     resultOr,
     resultNot,
     resultsAnd,
     resultsOr)
where

import PetriNet
import Structure

data Term a =
          Var a
        | Const Integer
        | Minus (Term a)
        | Term a :+: Term a
        | Term a :-: Term a
        | Term a :*: Term a
        deriving (Eq)

instance (Show a) => Show (Term a) where
        show (Var x) = show x
        show (Const c) = show c
        show (Minus t) = "-" ++ show t
        show (t :+: u) = "(" ++ show t ++ " + " ++ show u ++ ")"
        show (t :-: u) = "(" ++ show t ++ " - " ++ show u ++ ")"
        show (t :*: u) = show t ++ " * " ++ show u

instance Functor Term where
        fmap f (Var x) = Var (f x)
        fmap _ (Const c) = Const c
        fmap f (Minus t) = Minus (fmap f t)
        fmap f (t :+: u) = fmap f t :+: fmap f u
        fmap f (t :-: u) = fmap f t :-: fmap f u
        fmap f (t :*: u) = fmap f t :*: fmap f u

data Op = Gt | Ge | Eq | Ne | Le | Lt deriving (Eq)

instance Show Op where
        show Gt = ">"
        show Ge = "≥"
        show Eq = "="
        show Ne = "≠"
        show Le = "≤"
        show Lt = "<"

data Formula a =
          FTrue | FFalse
        | LinearInequation (Term a) Op (Term a)
        | Neg (Formula a)
        | Formula a :&: Formula a
        | Formula a :|: Formula a
             deriving (Eq)

infixr 3 :&:
infixr 2 :|:

instance (Show a) => Show (Formula a) where
        show FTrue = "true"
        show FFalse = "false"
        show (LinearInequation lhs op rhs) =
            show lhs ++ " " ++ show op ++ " " ++ show rhs
        show (Neg p) = "¬" ++ "(" ++ show p ++ ")"
        show (p :&: q) = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
        show (p :|: q) = "(" ++ show p ++ " ∨ " ++ show q ++ ")"

instance Functor Formula where
        fmap _ FTrue = FTrue
        fmap _ FFalse = FFalse
        fmap f (LinearInequation lhs op rhs) =
                LinearInequation (fmap f lhs) op (fmap f rhs)
        fmap f (Neg p) = Neg (fmap f p)
        fmap f (p :&: q) = fmap f p :&: fmap f q
        fmap f (p :|: q) = fmap f p :|: fmap f q

-- TODO: add functions to transform formula to CNF/DNF

data PropertyType = SafetyType
                  | LivenessType
                  | StructuralType
                  | ConstraintType

data ConstraintProperty = UniqueTerminalMarkingConstraint

data PropertyContent = Safety (Formula Place)
                  | Liveness (Formula Transition)
                  | Structural Structure
                  | Constraint ConstraintProperty

-- TODO: use Show instance
showPropertyType :: PropertyContent -> String
showPropertyType (Safety _) = "safety"
showPropertyType (Liveness _) = "liveness"
showPropertyType (Structural _) = "structural"
showPropertyType (Constraint _) = "constraint"

showConstraintProperty :: ConstraintProperty -> String
showConstraintProperty UniqueTerminalMarkingConstraint = "unique terminal marking"

showPropertyContent :: PropertyContent -> String
showPropertyContent (Safety f) = show f
showPropertyContent (Liveness f) = show f
showPropertyContent (Structural s) = show s
showPropertyContent (Constraint c) = showConstraintProperty c

data Property = Property {
        pname :: String,
        pcont :: PropertyContent
}

instance Show Property where
        show p =
            showPropertyName p ++
            " { " ++ showPropertyContent (pcont p) ++ " }"

renameProperty :: (String -> String) -> Property -> Property
renameProperty f (Property pn (Safety pf)) =
        Property pn (Safety (fmap (renamePlace f) pf))
renameProperty f (Property pn (Liveness pf)) =
        Property pn (Liveness (fmap (renameTransition f) pf))
renameProperty _ p = p

showPropertyName :: Property -> String
showPropertyName p = showPropertyType (pcont p) ++ " property" ++
               (if null (pname p) then "" else " " ++ show (pname p))

data PropResult = Satisfied | Unsatisfied | Unknown deriving (Show,Read,Eq)

resultAnd :: PropResult -> PropResult -> PropResult
resultAnd Satisfied x = x
resultAnd Unsatisfied _ = Unsatisfied
resultAnd _ Unsatisfied = Unsatisfied
resultAnd Unknown _ = Unknown

resultOr :: PropResult -> PropResult -> PropResult
resultOr Satisfied _ = Satisfied
resultOr _ Satisfied = Satisfied
resultOr Unsatisfied x = x
resultOr Unknown _ = Unknown

resultNot :: PropResult -> PropResult
resultNot Satisfied = Unsatisfied
resultNot Unsatisfied = Unsatisfied
resultNot Unknown = Unknown

resultsAnd :: [PropResult] -> PropResult
resultsAnd = foldr resultAnd Satisfied

resultsOr :: [PropResult] -> PropResult
resultsOr = foldr resultOr Unsatisfied
