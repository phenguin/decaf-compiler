{- Configuration.Types -- describing the overall behavior of the compiler
Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>

This file is a part of decafc.

decafc is free software: you can redistribute it and/or modify it under the
terms of the MIT (X11) License as described in the LICENSE file.

decafc is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the X11 license for more details. -}
module Configuration.Types where

--------------------------- The configuration type ----------------------------

data Configuration = Configuration { input :: FilePath
                                   , explicitTarget :: Maybe CompilerStage
                                   , debug :: Bool
                                   , opt :: OptimizationSpecification
                                   , explicitOutput :: Maybe FilePath
                                   } deriving (Eq)

defaultConfiguration :: Configuration
defaultConfiguration = Configuration { input = undefined
                                     , explicitTarget = Nothing
                                     , debug = False
                                     , opt = Some [] -- no optimizations
                                     , explicitOutput = Nothing
                                     }


------------------------------- Compiler stages -------------------------------

data CompilerStage = Scan
                   | Parse
                   | Inter
                   | Assembly
                   deriving (Eq, Ord)
instance Show CompilerStage where
  show Scan = "scan"
  show Parse = "parse"
  show Inter = "inter"
  show Assembly = "assembly"
instance Read CompilerStage where
  readsPrec _ "scan" = [(Scan, "")]
  readsPrec _ "parse" = [(Parse, "")]
  readsPrec _ "inter" = [(Inter, "")]
  readsPrec _ "assembly" = [(Assembly, "")]
  readsPrec _ _ = []


-------------------------- Describing optimizations ---------------------------

data OptimizationSpecification = All
                               | Some [OptimizationName]
                               deriving (Eq)

-- String might be the wrong type to use here, but whatever.
data OptimizationName = Enable String
                      | Disable String
                      deriving (Eq)
