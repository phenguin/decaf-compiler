module Optimization where

import Configuration
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import CodeGeneration
import Control.Monad.State
import Semantics
import MultiTree
import qualified Transforms as T
import qualified Data.Map as Map
import Control.Monad.State
import Data.List 
import Data.Char 
import Debug.Trace

toMidIR = progIR

allAsmOps:: [[AsmOp]->[AsmOp]]
allAsmOps = []
allIROps:: [(SemanticTreeWithSymbols->SemanticTreeWithSymbols)] 
allIROps = [optCSE]

doIROpts::Configuration -> SemanticTreeWithSymbols->SemanticTreeWithSymbols
doIROpts configuration irTree = (execState.mapM modify) opts irTree
			where opts = configToIROpts configuration

configToIROpts:: Configuration -> [(SemanticTreeWithSymbols->SemanticTreeWithSymbols)]
configToIROpts conf =   	case (opt conf) of
				(Some ops) -> map convertIR ops
				All -> allIROps

convertIR::OptimizationName -> (SemanticTreeWithSymbols->SemanticTreeWithSymbols)
convertIR (Enable str) = case str of 
			"cse" -> optCSE
			_     -> id
convertIR (Disable _) = id

doAsmOpts::Configuration -> [AsmOp] -> [AsmOp]
doAsmOpts configuration assList = (execState.mapM modify) opts assList
			where opts = configToAsmOpts configuration

configToAsmOpts:: Configuration -> [([AsmOp]->[AsmOp])]
configToAsmOpts conf =   	case (opt conf) of
				(Some ops) -> map convertAsm ops
				All -> allAsmOps

convertAsm::OptimizationName -> ([AsmOp]->[AsmOp])
convertAsm (Enable str) = case str of 
			_     -> id
convertAsm (Disable _) = id


optCSE::SemanticTreeWithSymbols->SemanticTreeWithSymbols 
optCSE= id --cse EmptyCSE execState (focusedTree tree)

data Program = Prg [Statement] deriving (Show,Eq) 
		
data Statement =  Set Variable Expression
		| If {ifCond::Expression , ifThen::[Statement] , ifElse::[Statement]}
		| While { condition::Expression , block::[Statement]}
		| Return Expression
		| Break 
		| Continue
		| DFun { 
			  functionName::String 
			, parameters::[Variable] 
			, body::[Statement]
			}
		| DVar Variable Expression
		| Callout {calloutName::String, calloutParams::[Expression]}
		| Function {functionName::String, params::[Expression]}
		deriving (Show,Eq) 

data Variable = Var {symbol::String}
		| Varray {symbol::String, index::Expression}
		deriving (Show,Eq) 

data Expression = Add {x::Expression, y::Expression}
		| Sub {x::Expression, y::Expression}
		| Mul {x::Expression, y::Expression}
		| Div {x::Expression, y::Expression}
		| Mod {x::Expression, y::Expression}
		| And {x::Expression, y::Expression}
		| Or {x::Expression, y::Expression}
		| Eq  {x::Expression, y::Expression}
		| Lt  {x::Expression, y::Expression}
		| Gt  {x::Expression, y::Expression}
		| Le  {x::Expression, y::Expression}
		| Ge  {x::Expression, y::Expression}
		| Ne  {x::Expression, y::Expression}
		| Not  {x::Expression}
		| Neg  {x::Expression}
		| Const Int
		| Str String
		| Loc Variable
		| FuncCall  {funcName::String, callParams::[Expression]}
		deriving (Show,Eq) 

progIR:: SemanticTreeWithSymbols -> Program
progIR (MT (_,T.Prog,st) block) = Prg $ concat $ map statementIR block

statementIR:: SemanticTreeWithSymbols -> [Statement]
statementIR (MT (_,(T.FD fdType (_,fdId)),st)  forest)= case fdType of
	T.Single -> [(DVar (Var (T.idString fdId)) val')]
	(T.Array size) -> [(DVar (Varray (T.idString fdId) (Const size)) val' )] 
	where val' = case forest of 
			(x:xs) -> (expressionIR $ head forest)
			[] -> (Const 0)
statementIR (MT (_,(T.MD (_,iD)),st)  forest)= [DFun (T.idString iD) params body]
	where 
	  params = map variableIR $ init forest
	  body = statementIR $ last forest
statementIR (MT (_,(T.CD _),st) _) = []

statementIR (MT (_,(T.Continue),st) _) = [Continue]

statementIR (MT (_,(T.Break),st) _) = [Break]

statementIR (MT (_,(T.Return),st) (val:_)) = [Return val']
	where
	  val' = expressionIR val

statementIR (MT (_,(T.Assign),st) (var:expression:_)) = [Set var' expression']
	where 
	  var' =  variableIR var
	  expression' = expressionIR expression 

statementIR (MT (_,(T.AssignPlus),st) (var:expression:_)) = [Set var' (Add (Loc var') expression')]
	where
	  var' =   variableIR var
	  expression' = expressionIR expression 

statementIR (MT (_,(T.AssignMinus),st) (var:expression:_)) = [Set var' (Sub (Loc var') expression')]
	where
	  var' =  variableIR var
	  expression' = expressionIR expression
 
statementIR (MT (_,T.If,st) (cond:ifthen:ifelse:_)) = [If cond' ifthen' ifelse']
	where
	  cond' = expressionIR cond
	  ifthen' = statementIR ifthen		
	  ifelse' = statementIR ifelse		

statementIR (MT (_,T.If,st) (cond:ifthen:_)) = [If cond' ifthen' []]
	where
	  cond' = expressionIR cond
	  ifthen' = statementIR ifthen		
	  
statementIR (MT (_,(T.MethodCall id'),st) params) =  case lookupSymbol id' st of
		(Just (CODesc)) -> [Callout (T.idString id') (map expressionIR params) ]
		(Just (MDesc _ _)) -> [Function (T.idString id') (map expressionIR params)] 
		Nothing -> []
statementIR (MT (_,T.While,st) (cond:body:_)) = [While cond' body']
	where
	  cond' = expressionIR cond
	  body' = statementIR body		

statementIR (MT (_,(T.For iD),st) (start:end:body:_)) = [Set i' (expressionIR start)] ++ [While cond' body']
	where
	  cond' = (Lt (Loc i') (expressionIR end))
	  body' = (statementIR body) ++ [Set i' (Add (Loc i') (Const 1))]
	  i'    = Var (T.idString iD) 

statementIR (MT (_,T.DBlock,st) body) = concat (map (statementIR) body)
	 
statementIR a = trace (show a) [(Break)]
 
expressionIR:: SemanticTreeWithSymbols -> Expression
expressionIR (MT (_,(T.MethodCall id'),st) params) =  FuncCall (T.idString id') (map expressionIR params) 

expressionIR (MT (_,(T.PD (_,iD)),st) _) = Loc (Var (T.idString iD))

expressionIR (MT (_,(T.DInt i),st) _) =  Const i 

expressionIR (MT (_,(T.DChar char),st) _) =  Const $ ord char 

expressionIR (MT (_,(T.DStr str),st) _) =  Str str 

expressionIR (MT (_,T.Add,st) (ex:ey:_)) =  Add x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Sub,st) (ex:ey:_)) =  Sub x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey


expressionIR (MT (_,T.Mul,st) (ex:ey:_)) =  Mul x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Div,st) (ex:ey:_)) =  Div x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Mod,st) (ex:ey:_)) =  Mod x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.And,st) (ex:ey:_)) =  And x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Or,st) (ex:ey:_)) =  Or x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Gt,st) (ex:ey:_)) =  Gt x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Lt,st) (ex:ey:_)) =  Lt x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Lte,st) (ex:ey:_)) =  Le x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Gte,st) (ex:ey:_)) =  Ge x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Eql,st) (ex:ey:_)) =  Eq x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Neql,st) (ex:ey:_)) =  Ne x' y'
	where 
	  x' =  expressionIR ex
	  y' =  expressionIR ey

expressionIR (MT (_,T.Not,st) (ex:_)) =  Not x'
	where 
	  x' =  expressionIR ex

expressionIR (MT (_,T.Neg,st) (ex:_)) =  Neg x'
	where 
	  x' =  expressionIR ex
expressionIR node@(MT (_,(T.Loc _),st) _) =  Loc (variableIR node)

expressionIR a = trace (show a) (Const 0)

variableIR:: SemanticTreeWithSymbols-> Variable
variableIR (MT (_,(T.Loc iD),_) forest) = case forest of 
		[] -> Var (T.idString iD)
		(x:xs) -> Varray (T.idString iD) (expressionIR x)

variableIR (MT (_,(T.PD (_,iD)),_) forest) = case forest of 
		[] -> Var (T.idString iD)
		(x:xs) -> Varray (T.idString iD) (expressionIR x)

variableIR a = trace (show a) (Var "ERROR!")

printMidIR (Prg sts) = map (pStat "#") sts
	where 
	  pStat pre (Set var expr) = putStrLn $ pre++(symbol var)++" = "++(show expr)
	  pStat pre (If cond thn els) = do 
						putStrLn $ pre++"if "++( show cond) 
						mapM (pStat (pre++"then|")) thn
						mapM (pStat (pre++"else|")) els
						return ()
	  pStat pre (While cond body) = do 
						putStrLn $ pre++"While "++(show cond) 
						mapM (pStat (pre++"    |")) body
						return ()
	  pStat pre (DFun name param body) = do 
						putStrLn $ pre++"def "++(show name) ++ (show param) 
						mapM (pStat (pre++"    |")) body
						return ()
	  pStat pre a = putStrLn $ pre++(show a)

---------------------------------------------------
-- CSE environment/state
---------------------------------------------------
{--
data CSEnv = CS CSEMap InScopeSet (IdEnv id)

emptyCSEnv = CS emptyUFM emptyInScopeSet emptyVarEnv

lookupCSEnv::CSEnv -> Expr -> Maybe Expre

loopupCSEnv (CS cs _ _) expr = case lookupMap cs (hashExpr expr) of
		Nothing -> Nothing
		Just pairs -> lookup_list pairs expr
lookup_list :: [(Expr,Expr)] -> Expr -> Maybe Expr
lookup_list [] _ = Nothing
lookup_list ((e,e'):es) expr 
		| exprEq e expr = Just e'
		| otherwise 	= lookup_list es expr

addCSEnvItem :: CSEnv -> CoreExpr -> CoreExpr -> CSEnv
addCSEnvItem env expr expr' 
		| exprIsBig expr = env
		| otherwise 	 = extendCSE env expr expr'

extendCSEnv ::CSEnv -> CoreExpr -> CoreExpr -> CSEnv
extendCSEnv (CS cs in_scope sub) expr expr'
		= CS (addToUFM_C combine cs hash [(expr,expr')]) in_scope sub
		where
			hash = hashExpr expr

---------------------------------------------------
-- CSE environment/state
---------------------------------------------------
data CSEnv = CS CSEMap InScopeSet (IdEnv id)

emptyCSEnv = CS emptyUFM emptyInScopeSet emptyVarEnv

lookupCSEnv::CSEnv -> Expr -> Maybe Expre

loopupCSEnv (CS cs _ _) expr = case lookupMap cs (hashExpr expr) of
		Nothing -> Nothing
		Just pairs -> lookup_list pairs expr
lookup_list :: [(Expr,Expr)] -> Expr -> Maybe Expr
lookup_list [] _ = Nothing
lookup_list ((e,e'):es) expr 
		| exprEq e expr = Just e'
		| otherwise 	= lookup_list es expr

addCSEnvItem :: CSEnv -> CoreExpr -> CoreExpr -> CSEnv
addCSEnvItem env expr expr' 
		| exprIsBig expr = env
		| otherwise 	 = extendCSE env expr expr'

extendCSEnv ::CSEnv -> CoreExpr -> CoreExpr -> CSEnv
extendCSEnv (CS cs in_scope sub) expr expr'
		= CS (addToUFM_C combine cs hash [(expr,expr')]) in_scope sub
		where
			hash = hashExpr expr
---------------------------------------------------
-- CSE environment/state
---------------------------------------------------
data CSEnv = CS CSEMap InScopeSet (IdEnv id)

emptyCSEnv = CS emptyUFM emptyInScopeSet emptyVarEnv

lookupCSEnv::CSEnv -> Expr -> Maybe Expre

loopupCSEnv (CS cs _ _) expr = case lookupMap cs (hashExpr expr) of
		Nothing -> Nothing
		Just pairs -> lookup_list pairs expr
lookup_list :: [(Expr,Expr)] -> Expr -> Maybe Expr
lookup_list [] _ = Nothing
lookup_list ((e,e'):es) expr 
		| exprEq e expr = Just e'
		| otherwise 	= lookup_list es expr

addCSEnvItem :: CSEnv -> CoreExpr -> CoreExpr -> CSEnv
addCSEnvItem env expr expr' 
		| exprIsBig expr = env
		| otherwise 	 = extendCSE env expr expr'

extendCSEnv ::CSEnv -> CoreExpr -> CoreExpr -> CSEnv
extendCSEnv (CS cs in_scope sub) expr expr'
		= CS (addToUFM_C combine cs hash [(expr,expr')]) in_scope sub
		where
			hash = hashExpr expr
---------------------------------------------------
-- CSE environment/state
---------------------------------------------------
data CSEnv = CS CSEMap InScopeSet (IdEnv id)

emptyCSEnv = CS emptyUFM emptyInScopeSet emptyVarEnv

lookupCSEnv::CSEnv -> Expr -> Maybe Expre

loopupCSEnv (CS cs _ _) expr = case lookupMap cs (hashExpr expr) of
		Nothing -> Nothing
		Just pairs -> lookup_list pairs expr
lookup_list :: [(Expr,Expr)] -> Expr -> Maybe Expr
lookup_list [] _ = Nothing
lookup_list ((e,e'):es) expr 
		| exprEq e expr = Just e'
		| otherwise 	= lookup_list es expr

addCSEnvItem :: CSEnv -> CoreExpr -> CoreExpr -> CSEnv
addCSEnvItem env expr expr' 
		| exprIsBig expr = env
		| otherwise 	 = extendCSE env expr expr'

extendCSEnv ::CSEnv -> CoreExpr -> CoreExpr -> CSEnv
extendCSEnv (CS cs in_scope sub) expr expr'
		= CS (addToUFM_C combine cs hash [(expr,expr')]) in_scope sub
		where
			hash = hashExpr expr
			combine o n = n++o

lookupSubst (CS _ _ sub) x = case lookupVarEnv sub x of 
				Just y  -> y 
				Nothing -> x

extendSubst :: CSEnv -> Id -> (CSEnv,Id)
extendSubst (CS cs in_scope sub) x y = CS cs in_scope (extendVarEnc sub )
addBinder (CS cs in_scope sub) v
	| 


--------------------------------------------------------------------
--		CSE 
--------------------------------------------------------------------

cseProgram binds = cseBinds emptyCSEnv binds

cseBinds _ [] = []
cseBinds env (b:bs) = (b':bs')
		where
			(env1,b') = cseBind env b
			bs'	  = cseBinds env bs

cseBind env (NonRec b e) = let (env',(b',e')) = do_one env (b, e)
				in (env',NonRec b' e')
cseBind env (Rec pairs =

do_one env (id,rhs) 
	= case LookupCSEnv env rhs' of
		Just (Var other_id) -> (extendSubst env' id other_id, (id',Var other_id))
		Just other_expr     -> (env' , (id', other_expr)
		Nothing 	    -> (addCSEnvItem env' rhs' (Var id'),(id',rhs'))
	where
	  (env' , id') = addBinder env id
	  rhs' 	| isAlwaysActive (idInlineAvtivation id) = cseExpr env' rhs
		| otherwise				 = rhs

tryForCSE _ (Type t) = Type t 
tryForCSE env expr   = case lookupCSEnv env expr' of
			  Just smaller_expr -> smaller_expr
			  Nothing		  -> expr'
			where
			  expr' = cseExpr env expr

cseExpr _ (Type t)	= Type t
cseExpr _ (Lit lit) 	= Lit lit
cseExpr env (Var v)	= Var (lookupSubst env v) 
cseExpr env (App f a)	= App (cseExpr env f) (tryForCSE env a)

data CSEState = EmptyCSE | CS (Map.Map SemanticTreeWithSymbols SemanticTreeWithSymbols)

cse env node = 
cse env node = (MT (p,Prog,s) block')		
		where block' = map (cse EmptyCSE) block
cse env node@(MT (p,AssignPlus,s) assign) = (MT (p,AssignPlus,s) assign')
		where (env',assign') = cseAssign env assign
cse env node@(MT a forest)= (MT a forest')
		where forest' = map (cse env) forest

cse node@(MT block forest) = do 
	foreach chid in forest:
		expressions <- get
		if node in expressions
			then replace it
		clobber if assignment
		create newexpression variables
		put newexpressions
		recurse
	return output
 
CSE


-- takes expression determines what must be removed from the expressions state 
clobber 

-- equivalence checker
equivalent expr expr
		

--}

-- Pretty printing..

instance PrettyPrint Expression where
    ppr (Add e1 e2) = parens $ (ppr e1) <+> text "+" <+> (ppr e2)
    ppr (Sub e1 e2) = parens $ (ppr e1) <+> text "-" <+> (ppr e2)
    ppr (Mul e1 e2) = parens $ (ppr e1) <+> text "*" <+> (ppr e2)
    ppr (Div e1 e2) = parens $ (ppr e1) <+> text "/" <+> (ppr e2)
    ppr (Mod e1 e2) = parens $ (ppr e1) <+> text "%" <+> (ppr e2)
    ppr (And e1 e2) = parens $ (ppr e1) <+> text "&&" <+> (ppr e2)
    ppr (Or e1 e2) = parens $ (ppr e1) <+> text "||" <+> (ppr e2)
    ppr (Eq e1 e2) = parens $ (ppr e1) <+> text "==" <+> (ppr e2)
    ppr (Lt e1 e2) = parens $ (ppr e1) <+> text "<" <+> (ppr e2)
    ppr (Gt e1 e2) = parens $ (ppr e1) <+> text ">" <+> (ppr e2)
    ppr (Le e1 e2) = parens $ (ppr e1) <+> text "<=" <+> (ppr e2)
    ppr (Ge e1 e2) = parens $ (ppr e1) <+> text ">=" <+> (ppr e2)
    ppr (Ne e1 e2) = parens $ (ppr e1) <+> text "!=" <+> (ppr e2)
    ppr (Not e) = text "!" <+> parens (ppr e)
    ppr (Neg e) = text "-" <+> parens (ppr e)
    ppr (Const i) = int i
    ppr (Str s) = text $ show s
    ppr (Loc v) = ppr v
    ppr (FuncCall name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma

instance PrettyPrint Variable where
    ppr (Var name) = text name
    ppr (Varray name e) = text name <> lbrack <+>
                          ppr e <+> rbrack

instance PrettyPrint Statement where
    ppr (If _ _ _) = text "If Statement which shouldnt be here"
    ppr (While _ _) = text "While Statement which shouldn't be here"
    ppr (Return e) = text "return" <+> ppr e
    ppr Break = text "break"
    ppr Continue = text "continue"
    ppr (Set v e) = ppr v <+> text "=" <+> ppr e
    ppr (DVar v e) = ppr v <+> text "=" <+> ppr e
    ppr (Function name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma
    ppr (Callout name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma
