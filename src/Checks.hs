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
            , checkIdenifierDeclared
	    , checkForLoops
	    , checkMethodCallParameters
	    , checkMethodReturnStatement
	    , checkBreakContinue
	    , checkMain
	    , checkAssignOperators
        , checkArrayLocAccessesValid
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
      where childrenTypes = (map expressionType childrenMinusCallouts)
            childrenMinusCallouts = filter isNotCO children
	    isNotCO (MT(_,(MethodCall id),s) _) =
		case lookupSymbol id s of
			(Just CODesc) -> False
			otherwise -> True 
	    isNotCO _ = True
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
                                    Just md@(MDesc _ _) -> xs == paramTypeList md
				    Just md@(CODesc)    -> True
                                    _ -> False

--1 --- Not implementable because of hashmap
--2 -}
identifierDeclared 
	(MT (pos, (Loc id) ,st) _)= 
		case symbolTableContains id st of
			True 	-> Down Nothing
			False 	-> Down $ Just$ (show pos) ++ "Identifier " ++ (idString id) ++ " is undeclared"
identifierDeclared 
	_ = Down Nothing

checkIdenifierDeclared p = traverse identifierDeclared p 

-- Semantic Check #4
arrayBoundsValid :: SemanticTreeWithSymbols -> TraverseControl
arrayBoundsValid (MT (pos, (FD (Array n) _), _) _) = case n <= 0 of
    True -> Down $ Just $ show (pos) ++ ": Array must have positive integer size"
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
checkParameterTypes st id param2 = case (fromJust $ lookupSymbol id st ) of
					(MDesc _ param1) -> (all (\(a,b)->a==b) (zip param1 param2))
					(CODesc) -> True
					otherwise -> False
methodCallParameterMatch 
	node@(MT (pos, (MethodCall id), st) forest )= 
			if  (symbolTableContains id st)&& (checkParameterTypes st id params)
				then Down Nothing
				else Up $ Just $ (show pos) ++ "Method " ++ (idString id) ++ " parameter type error"					
		where  	params = map extractType $ filter (isParam) forest--(paramTypes node) 
			extractType (MT (pos , (PD (t,_)) ,_)_) = t
			isParam (MT (pos, (PD _) ,_)_) = True
			isParam _ = False
methodCallParameterMatch _ = Down Nothing 

checkMethodCallParameters p = 
	traverse methodCallParameterMatch p 

--8/9 method return statements.

methodReturnStatement
	(MT (pos, (MD (lt, id)), st) forest) =
		case Data.Either.lefts returnTypes of
			[]	-> Up $ if and [lt == rt | rt <- Data.Either.rights returnTypes]
						then Nothing
						else Just $ (show pos) ++ "invalid return"
			_	-> Down $Just$ foldr (\ a b -> a ++ "\n" ++ b) "" $ Data.Either.lefts returnTypes
		where 	
        returnTypes = map returnType (filter isReturn $ children block)
        isReturn (MT(_, Return, _) _) = True
        isReturn _ = False
        isBlock (MT(_, DBlock, _) _) = True
        isBlock _ = False
        returnType (MT(pos, Return, st) forest) = case forest of 
            []	-> Right VoidType
            _	-> expressionType (head forest)
        block = head $ filter isBlock forest

methodReturnStatement _ = Down Nothing
checkMethodReturnStatement p =
	traverse methodReturnStatement p

-- 10 This is checked coincidentally by check #2.

-- 11 Check id[expr] syntax for validity
arrayLocAccessValid :: SemanticTreeWithSymbols -> TraverseControl
arrayLocAccessValid (MT (pos, Loc id, _) []) = Down Nothing
arrayLocAccessValid (MT (pos, Loc id, st) (idx:xs)) = 
    case isArrayLoc id && (expressionType idx == Right IntType) of
        True -> Down Nothing
        False -> Down $ Just $ show pos ++ ": Invalid array index operation."
    where 
        isArrayLoc s = case lookupSymbol s st of
            Just (FDesc (Array _) _) -> True
            _ -> False
arrayLocAccessValid _ = Down Nothing

checkArrayLocAccessesValid = traverse arrayLocAccessValid

assignCheck node@(MT (pos, (Assign), st) forest) = 
	if allequal || containsCO 
		then Up Nothing
		else Up $ Just $ (show pos)++"Assign operator type mismatch"
	where 	allequal = case partitionEithers childrenType of
				([],rightTypes) -> (and $ map (\ x -> (head rightTypes) == x) rightTypes) && arraycheck
				otherwise  ->  False
		childrenType = map expressionType forest
		arraycheck = null ( filter arrs (tail forest))
		arrs (MT (pos,(Loc id),s) index ) = case (lookupSymbol id st) of
				Just (FDesc (Array _) _) -> null index
				otherwise -> False
		arrs _ = False
		containsCO = not $ null $traverse cos node
		cos (MT (pos, (MethodCall id) , st) _ )= case (lookupSymbol id st) of
			Just CODesc -> Up $Just "CALLOUT!"
			otherwise -> Down Nothing 
		cos _ = Down Nothing
assignCheck (MT (pos, (AssignPlus), _) forest) =
	if allint
		then Up Nothing
		else Up $ Just $ (show pos)++"Assign operator type mismatch"
	where 	allint = case partitionEithers childrenType of
				([],rightTypes) -> and $ map (\ x -> x == IntType) rightTypes
				otherwise  ->  False
		childrenType = map expressionType forest
assignCheck (MT (pos, (AssignMinus), _) forest) =
	if allint 
		then Up Nothing
		else Up $ Just $ (show pos)++"Assign operator type mismatch"
	where 	allint = case partitionEithers childrenType of
				([],rightTypes) -> and $ map (\ x -> x == IntType) rightTypes
				otherwise  ->  False
		childrenType = map expressionType forest

assignCheck _ = Down Nothing

checkAssignOperators = traverse assignCheck

forCheck (MT (pos, (For t), st ) forest) =
	case subExpressionTypes of
		([],x) -> if all (==IntType)$ (symbolType t st):x
				then Down Nothing
				else Up $Just $ (show pos) ++ "Malformed For loop"
		otherwise-> Up $Just $ (show pos) ++ "Malformed For loop"
	where	subExpressionTypes = partitionEithers (map expressionType (take 2 forest))
forCheck _ = Down Nothing				
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
breakContinue _ = Down Nothing
checkBreakContinue p =
	traverse breakContinue p

findMain
	(MT (pos,(MD (_,(IdWithHash _ "main"))),_) _) = Up $Just "MAIN"
findMain _ = Down Nothing

checkMain p = case (traverse findMain p) of
		["MAIN"] -> []
		otherwise -> ["Main is not defined"]
