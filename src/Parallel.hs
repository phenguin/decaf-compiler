module Parallel where
import Santiago

firefuel = "HI"

parallelize = id


solveLinearInteger x y z 
	| z == 0 = 0
	| y == 0 = 0
	| otherwise = 	let v = solveLinearInteger y (mod x y) (mod z y)
		       	in solveForX x y z v

solveForX x y z v = (-z -(y*v)) / x

getGCD x y = gcd x y




	
