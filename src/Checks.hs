module Checks where

import Data.Maybe
import Prelude
import MultiTree

expand (MT _ a ) = a

traverse f tree = case (f tree ) of
	Just b -> b
	Nothing -> and checkedChildren
	where 	children = expand tree
		checkedChildren = map (traverse f) children

symbolTableContains:: ST -> Identifier-> Bool 
symbolTableContains st symb = 

--1 --- Not implementable because of hashmap
--2
identifierDeclared 
	(MT (pos, (Loc id ) ,st) _)= 
		case symbolTableContains st id of
			True 	-> nothing
			False 	-> False
identifierDeclared 
	_ = Nothing

checkIdenifierDeclared p = traverse identifierDeclared p 
--5 parameter type check
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

