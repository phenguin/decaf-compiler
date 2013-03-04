module Checks where

import Data.Maybe
import Data.Either (partitionEithers, lefts, rights)
import Prelude
import MultiTree
import Traverse
import Data.List (nub)
import Semantics
import Transforms
import Util (testParse)

-- Utility functions for semantic checking
checkParse :: String -> SemanticTreeWithSymbols
checkParse s = addSymbolTables $convert $fromRight $testParse s

symbolTableContains:: Id -> SymbolTable -> Bool 
symbolTableContains id st = isJust $ lookupSymbol id st

idString:: Id -> String
idString id@(IdWithHash _ s) = s

type SemanticCheck = SemanticTreeWithSymbols -> [String]

doChecks :: [SemanticCheck] -> SemanticTreeWithSymbols -> Either String [IO ()]
doChecks fs t = let errs = concat $ map (\f -> f t) fs in do
    case errs of
        [] -> Right []
        _ ->  Left $ "\n" ++ unlines errs

-- List the checks you want to be applied here. Main.hs pulls this var
checksList :: [SemanticCheck]
checksList = [checkArrayBoundsValid
            , checkCondsHaveBoolType
            , checkArithRelOpOperandTypes
            ]

testCheck c = doChecks [c] . checkParse

-- Implementations of specific semantic checks below here

paramTypes :: SemanticTreeWithSymbols -> [LitType]
paramTypes (MT (pos, (MD _) ,_) ts) = Prelude.map f $ Prelude.filter g ts
    where g (MT (pos, (PD _), _) _) = True
          g _ = False
          f (MT (pos, (PD (t, i)),_) _) = t
          f _ = VoidType -- Hackish

paramTypes (MT (pos, (MethodCall _) ,_) ts) = Prelude.map f ts
    where f (MT (pos, (PD (t, i)),_) _) = t
	  f (MT (pos , (DInt _),_)_) = IntType
	  f (MT (pos , (DBool _),_)_) = BoolType
	  f (MT (pos , (DChar _),_)_) = IntType
          f _ = VoidType -- Hackish
          --
expressionType:: SemanticTreeWithSymbols -> Either String LitType
expressionType node@(MT (pos, exp , st) children) =  if null ls && (childsTypePred node) rs then Right expectType else Left $ "Expression type error"
      where childrenTypes = (map expressionType children)
            expectType = expectedType node
            (ls, rs) = partitionEithers childrenTypes 

symbolType:: Id -> SymbolTable -> LitType
symbolType id st = case (lookupSymbol id st) of
			(Just (FDesc _ tp)) 	-> tp
			(Just (MDesc tp  _))	-> tp
			(Just (PDesc tp )) 	-> tp
			otherwise	-> VoidType

expectedType:: SemanticTreeWithSymbols -> LitType
expectedType (MT (_,node ,st) _)  = case node of
            MethodCall id	-> symbolType id st
            And			-> BoolType
            Or			-> BoolType
            Add			-> IntType
            Sub			-> IntType
            Mul			-> IntType
            Mod			-> IntType
            Div			-> IntType
            Not 		-> BoolType
            Neg			-> IntType
            Neql		-> BoolType
            Eql			-> BoolType
            Lt			-> BoolType
            Lte			-> BoolType
            Gt			-> BoolType
            Gte			-> BoolType
            Loc id		-> symbolType id st
            DChar _		-> IntType
            DInt _		-> IntType
            DBool _		-> BoolType

childsTypePred:: SemanticTreeWithSymbols -> [LitType] -> Bool
childsTypePred (MT (_,node ,st) _)  = case node of
            MethodCall id	-> mcCheck id
            And			-> allBool
            Or			-> allBool
            Add			-> allInt
            Sub			-> allInt
            Mul			-> allInt
            Mod			-> allInt
            Div			-> allInt
            Not 		-> allBool
            Neg			-> allInt
            Neql		-> allSame
            Eql			-> allSame
            Lt			-> allInt
            Lte			-> allInt
            Gt			-> allInt
            Gte			-> allInt
            Loc id		-> allInt
            otherwise   -> const True
        where allBool = all (== BoolType)
              allInt = all (== IntType)
              allSame xs = length (nub xs) <= 1
              mcCheck id xs = let res = lookupSymbol id st in
                               case res of
                                    Nothing -> False
                                    Just md -> xs == paramTypeList md

--1 --- Not implementable because of hashmap
--2 -}
identifierDeclared 
	(MT (pos, (Loc id ) ,st) _)= 
		case symbolTableContains id st of
			True 	-> Down Nothing
			False 	-> Down $ Just$ (show pos) ++ "Identifier " ++ (idString id) ++ " is undeclared"
identifierDeclared 
	_ = Down Nothing

checkIdenifierDeclared p = traverse identifierDeclared p 

-- Semantic Check #4
arrayBoundsValid :: SemanticTreeWithSymbols -> TraverseControl
arrayBoundsValid (MT (pos, (FD (Array n) (t, id)), st) _) = case n <= 0 of
    True -> Down $ Just $ show (pos) ++ ": Invalid array declaration for " ++ (idString id) ++ ".  Array must have positive integer size"
    False -> Down Nothing
arrayBoundsValid _ = Down Nothing

checkArrayBoundsValid = traverse arrayBoundsValid

-- Semantic Check #12
condHasBoolType :: SemanticTreeWithSymbols -> TraverseControl

condHasBoolType (MT (pos, If, st) (x:xs)) = case expressionType x of
    Right BoolType -> Down Nothing
    _ -> Down $ Just $ show pos ++ ": If conditional expr must have type bool"

condHasBoolType (MT (pos, While, st) (x:xs)) = case expressionType x of
    Right BoolType -> Down Nothing
    _ -> Down $ Just $ show pos ++ ": While conditional expr must have type bool"

condHasBoolType _ = Down Nothing

checkCondsHaveBoolType = traverse condHasBoolType

-- Semantic Check #13
typecheckArithRelOps :: SemanticTreeWithSymbols -> TraverseControl

typecheckArithRelOps node@(MT (pos, x, st) _) 
    | x `elem` opList = case expressionType node of
        Right _  -> Down Nothing
        Left _ -> Down $ Just $ show pos ++ ": Arithmetic and Relational ops operands must have int types"
    | otherwise = Down Nothing
    where opList = [Add, Sub, Mul, Mod, Div, Gt, Gte, Lt, Lte]

checkArithRelOpOperandTypes = traverse typecheckArithRelOps

-- 5 parameter type check
checkParameterTypes:: SymbolTable -> Id ->[LitType] -> Bool
checkParameterTypes st id param2 = (param1 == param2)
			where 	(MDesc _ param1) = fromJust $ lookupSymbol id st

methodCallParameterMatch 
	node@(MT (pos, (MethodCall id), st) forest )= 
			if  (symbolTableContains id st)&& (checkParameterTypes st id params)
				then Down Nothing
				else Up $ Just $ (show pos) ++ "Method " ++ (idString id) ++ " parameter type error"					
		where  params = (paramTypes node) 
methodCallParameterMatch _ = Down Nothing 

checkMethodCallParameters p = 
	traverse methodCallParameterMatch p 

--8/9 method return statements.

methodReturnStatement
	(MT (pos, (MD (lt, id)), st) forest) =
		case Data.Either.lefts returnTypes of
			[]	-> Down $ if and [lt == rt | rt <- Data.Either.rights returnTypes]
						then Nothing
						else Just $ (show pos) ++ "invalid return"
			_	-> Down $Just$ foldr (\ a b -> a ++ "\n" ++ b) "" $ Data.Either.lefts returnTypes
		where 	returnTypes = map returnType (filter isReturn forest)
			isReturn (MT(_, Return, _) _) = True
			isReturn _ = False
			returnType (MT(pos, Return, st) forest) = case forest of 
				[]	-> Right VoidType
				_	-> expressionType (head forest)


checkMethodReturnStatement p =
	traverse methodReturnStatement p
{-
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

-}

forCheck (MT (pos, (For t), st ) forest) =
	case subExpressionTypes of
		([],x) -> if all (==IntType)$ (symbolType t st):x
				then Down Nothing
				else Up $Just $ (show pos) ++ "Malformed For loop"
		otherwise-> Up $Just $ (show pos) ++ "Malformed For loop"
	where	subExpressionTypes = partitionEithers (map expressionType (take 2 forest))
					
checkForLoops p = traverse forCheck p 
-- 19 Break/Continue checks

breakContinue
	(MT (pos, Break, st) forest) = Up $ Just "Cannot have break statement outside of a loop."
breakContinue
	(MT (pos, Continue, st) forest) = Up $ Just "Cannot have continue statement outside of a loop."
breakContinue
	(MT (pos, For t, st) forest) = Up Nothing
breakContinue
	(MT (pos, While, st) forest) = Up Nothing

breakContinueCheck p =
	traverse breakContinue p



