module Checks where

import Data.Maybe
import Prelude
import MultiTree
import Traverse
import Semantics
import Transforms
import Main(testParse)
-- Utility functions for semantic checking
checkParse :: String -> SemanticTreeWithSymbols
checkParse s = addSymbolTables $convert $fromRight $testParse s

symbolTableContains:: Id -> SymbolTable -> Bool 
symbolTableContains id st = isJust $ lookupSymbol id st

idString:: Id -> String
idString id@(IdWithHash _ s) = s



--1 --- Not implementable because of hashmap
--2
identifierDeclared 
	(MT (pos, (Loc id ) ,st) _)= 
		case symbolTableContains id st of
			True 	-> Down Nothing
			False 	-> Down $ Just$ "Identifier " ++ (idString id) ++ " is undeclared"
identifierDeclared 
	_ = Down Nothing

checkIdenifierDeclared p = traverse identifierDeclared p 


{- 5 parameter type check
checkParameterTypes st param2 = ?????? 

methodCallParameterMatch 
	(MT (pos, (MethodCall id), st) forest )= 
			if checkParameterTypes st pds 
				then Nothing
				else Just False					
		where 
			parameters = map extractPD pdNodes 
			extractPD (MT (pos,pd,st) _) = pd
			pdNodes = filter isPD forest
			isPD (MT (pos, (PD _), st) _) = True
			isPD _ = False

checkMethodCallParameters p = 
	traverse methodCallParameterMatch p 

--8/9 method return statements.

methodReturnStatement
	(MT (pos, (MD (lt, id)), st) forest) =
		case lefts returnTypes of
			[]	-> Right $ all [lt == rt | rt <- rights returnTypes]
			_	-> Left $ fold (\ a b = a ++ "\n" ++ b) $ lefts returnTypes
		where 	returnTypes = map returnType (filter isReturn forest)
			isReturn (MT(_, Return, _) _) = True
			isReturn _ = False
			returnType (MT(pos, Return, st) forest) = case forest of 
				[]	-> Right VoidType
				_	-> expressionType st $ head forest


checkMethodReturnStatement p =
	traverse methodReturnStatement p

-- 10 This is checked coincidentally by check #2.

-- 11 Check id[expr] syntax for validity

arrayLocationValidity
	(MT (pos, (Loc id), st) forest) =
		case forest of
			-- Singleton location eg "x"
			[]	-> Right Nothing
			-- Array index location eg "x[5]"
			_	-> if varType != Array
					then Left "Cannot lookup index of non-array."
					else
						case indexType of
							Left	-> indexType
							Right	-> if (fromRight indexType) == IntType
									then Right Nothing
									else Left "Cannot lookup non-integer index of array."
			where	varType		= symbolTableType st id
				indexType 	= expressionType st $ head forest

checkArrayLocationValidity p =
	traverse arrayLocationValidity p

-- 12 Expressions within if or while statements must be booleans.

ifWhileConditionBoolean
	(MT (pos, t, st) forest) =
		case t of
			If	-> isBoolean
			While	-> isBoolean
			_	-> Right Nothing
		where	isBoolean = case conditionType of
				Left	-> conditionType
				Right	-> if (fromRight conditionType) == BoolType
						then Right Nothing
						else Left "Cannot use non-boolean condition in control statement."
			conditionType	= expressionType st $ head forest
			conditionBlock	= head forest

checkIfWhileConditionBoolean p =
	traverse ifWhileConditionBoolean p

-- 13 The operands of arithmetic operations (+, -, etc.) and relative operations (<, >=, etc.) have to be integers.
-- @TODO: Are we supposed to consider the negation operation here too?
integerOperation
	(MT (pos, t, st) forest@(a:b:_)) =
		case t of
			Add	-> integerOperands
			Sub	-> integerOperands
			Mul	-> integerOperands
			Div	-> integerOperands
			Mod	-> integerOperands
			Lt	-> integerOperands
			Lte	-> integerOperands
			Gt	-> integerOperands
			Gte	-> integerOperands
			_	-> Right Nothing
		where 	integerOperands = case aType of
				Left	-> aType
				Right	-> case bType of
					Left	-> bType
					Right	-> if (fromRight aType) == IntType
						then if (fromRight bType) == IntType
							then Right Nothing
							else Left errorMsg
						else Left errorMsg
			aType		= expressionType st a
			bType		= expressionType st b
			errorMsg	= "Cannot use non-integer in strictly integer operation."

checkIntegerOperation p =
	traverse integerOperation p

-- 14 The operands of eq-ops must have the same type, either int or boolean.

equalityOperation
	(MT (pos, t, st) forest@(a:b:_)) =
		case t of
			Eql	-> eqOperands
			Neql	-> eqOperands
			_	-> Right Nothing
		where	eqOperands = case aType of
				Left	-> aType
				Right	-> case bType of
					Left	-> bType
					Right	-> if (fromRight aType) != (fromRight bType)
							then Left "Cannot compare values of different types."
							else if (fromRight aType) != IntType && (fromRight aType) != BoolType
								then Left "Cannot compare values unless they are integers or booleans."
								else Right Nothing
			aType 	= expressionType st a
			bType	= expressionType st b

checkEqualityOperation p =
	traverse equalityOperation p

-- 15 The operands of cond ops and the operand of logical not (!) must have type boolean

booleanOperation
	(MT (pos, t, st) forest) =
		case t of
			And	-> booleanOperands
			Or	-> booleanOperands
			Not	-> booleanOperand
		where	booleanOperands = case aType of
				Left	-> aType
				Right	-> case bType of
					Left	-> bType
					Right	-> if (fromRight aType) == BoolType && (fromRight bType) == BoolType
							then Right Nothing
							else Left errorMsg
			booleanOperand = case aType of
				Left	-> aType
				Right	-> if (fromRight aType) == BoolType
						then Right Nothing
						else Left errorMsg
			aType	= expressionType st a
			bType	= expressionType st b
			a	= forest !! 0
			b	= forest !! 1
			errorMsg= "Cannot use non-boolean in strictly boolean operation."

booleanOperationCheck p =
	traverse booleanOperation p

-- 16 Assignment ops
-- TODO: I am confused how to properly get the operands ("location" and "expression") for the assignment operation. -Charlie

assignmentType
	(MT (pos, (Assign id), st) forest) =
		case exprType of
			Left -> exprType
			Right -> if (fromRight exprType) == locationType
				then Right Nothing
				else Left "Cannot assign expression to location of a different type."
		where	locationType	= symbolTableType st location
			exprType	= expressionType st expr
			location	= ?????
			expr		= ????????

assignmentTypeCheck p =
	traverse assignmentType p

-- 17 Increment/decrement assign operation must be integers
-- TODO: I am confused how to properly get the operands ("location" and "expression") for the assignment operation. -Charlie

incrementDecrementAssign
	(MT (pos, t, st) forest) =
		case t of
			AssignPlus -> assignOp
			AssignMinus -> assignOp
		where	assignOp 	= case exprType of
				Left -> exprType
				Right -> if (fromRight exprType) == IntType && locationType == IntType
						then Right Nothing
						else Left "Cannot increment or decrement with non-integers."
			locationType	= symbolTableType st location
			exprType	= expressionType st expr
			location	= ????
			expression	= ??????

incrementDecrementAssignCheck p =
	traverse incrementDecrementAssign p

-- 18 TODO For statement integer checks


-- 19 Break/Continue checks

breakContinue
	(MT (pos, Break t, st) forest) = Left "Cannot have break statement outside of a loop."
breakContinue
	(MT (pos, Continue t, st) forest) = Left "Cannot have continue statement outside of a loop."
breakContinue
	(MT (pos, For t, st) forest) = Right True
breakContinue
	(MT (pos, While t, st) forest) = Right True

breakContinueCheck p =
	traverse breakContinue p
-}
