{-# LANGUAGE DeriveDataTypeable #-}
module MidIR where

import Varmarker
import Configuration
import Data.Data
import Data.Typeable
import PrettyPrint
import Text.PrettyPrint.HughesPJ hiding (Str)
import Control.Monad.State
import Semantics
import MultiTree
import qualified Transforms as T
import qualified Data.Map as Map
import Control.Monad.State
import Transforms (FDType, FDType(..))
import Data.List 
import Data.Char 
import Debug.Trace

toMidIR = progIR

data Program = Prg {getCode::[Statement]} deriving (Show,Eq,Data,Typeable) 
		
data Statement =  Set Variable Expression
		| If {ifCond::Expression , ifThen::[Statement] , ifElse::[Statement]}
		| While { condition::Expression , block::[Statement]}
		| ForLoop  {inductionVar::Variable, startVal::Expression , endVal::Expression, block::[Statement]}
		| Parafor  {inductionVar::Variable, startVal::Expression ,endVal::Expression, block::[Statement]}
		| Scar String -- when for loops are castrated out of the tree for parallelization
		| Return Expression
		| Break 
		| Continue
		| DFun { 
			  functionName::String 
			, parameters::[Variable] 
			, body::[Statement]
			}
		| DVar Variable 
		| Callout {calloutName::String, calloutParams::[Expression]}
		| Function {functionName::String, params::[Expression]}
		deriving (Show,Eq,Ord, Data, Typeable) 

data Variable = Var {getSymbol::String}
		| Varray {getSymbol::String, index::Expression}
		| Scopedvar {getScope::[Scoped] , getVar::Variable}
		deriving (Show,Eq, Ord, Data, Typeable) 

varToVarMarker :: Variable -> VarMarker
varToVarMarker (Var name) = VarMarker name Transforms.Single []
-- TODO: FDType of Array 0 doesn't accurately reflect whats going on here.
varToVarMarker (Varray name _) = VarMarker name (Transforms.Array 0) []
varToVarMarker (Scopedvar s v) = setScope s $ varToVarMarker v
symbol :: Variable -> String
symbol (Scopedvar _ v) = symbol v
symbol var = getSymbol var

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
		| Loc {var::Variable}
		| FuncCall  {funcName::String, callParams::[Expression]}
		deriving (Show,Eq, Ord, Data, Typeable) 

scrapeGlobals prg = globalvars
	where 	dvars = filter isDVar (getCode prg)
		isDVar x@(DVar _) = True 
		isDVar x = False
		globalvars = map (\(DVar a) -> a) dvars


progIR:: SemanticTreeWithSymbols -> Program
progIR (MT (_,T.Prog,st) block) = Prg $ concat $ map statementIR block

statementIR:: SemanticTreeWithSymbols -> [Statement]
statementIR (MT (_,(T.FD fdType (_,fdId)),st)  forest)= case fdType of
	T.Single -> [(DVar (Var (T.idString fdId)) )]
	(T.Array size) -> [(DVar (Varray (T.idString fdId) (Const size)) )] 
statementIR (MT (_,(T.MD (_,iD)),st)  forest)= [DFun (T.idString iD) params ((map DVar params)++body)]
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

statementIR (MT (_,(T.For iD),st) (start:end:body:_)) =(Set i' start' ):[ForLoop i' start' end' body']
	where
	  start' = (expressionIR start)
	  end' = (expressionIR end)
	  body' = (statementIR body) ++ [(Set i' (Add (Loc i') (Const 1)))]
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
    ppr (Scopedvar scope v) = text (show scope) <+> ppr v

instance PrettyPrint Statement where
    ppr (If _ _ _) = text "If Statement which shouldnt be here"
    ppr (While _ _) = text "While Statement which shouldn't be here"
    ppr (Return e) = text "return" <+> ppr e
    ppr Break = text "break"
    ppr Continue = text "continue"
    ppr (Set v e) = ppr v <+> text "=" <+> ppr e
    ppr (DVar v ) = ppr v
    ppr (Function name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma
    ppr (Callout name ps) = text name <+> prettyParams
        where prettyParams = foldl f lparen ps <+> rparen
              f acc p = acc <+> ppr p <> comma
    ppr (DFun name params _) = text "Method Declaration:" <+> text name
