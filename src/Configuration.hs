{- Configuration -- describing the overall behavior of the compiler
Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>

This file is a part of decafc.

decafc is free software: you can redistribute it and/or modify it under the
terms of the MIT (X11) License as described in the LICENSE file.

decafc is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the X11 license for more details. -}
module Configuration ( Configuration
                     , input, target, debug, opt, output
                     , defaultConfiguration
                     , CompilerStage(..)
                     , OptimizationSpecification(..)
                     , OptimizationName(..)
                     ) where

import Data.Maybe (fromMaybe)
import System.FilePath (replaceExtension)

import Configuration.Types ( Configuration(..)
                           , input, debug, opt
                           , explicitTarget, explicitOutput
                           , defaultConfiguration
                           , CompilerStage(..)
                           , OptimizationSpecification(..)
                           , OptimizationName(..)
                           )


--------------------------- The configuration type ----------------------------
{- 'input', 'debug', and 'opt' are fine accessor functions.  'target' and
'output', on the other hand, is a bit special. -}

target :: Configuration -> CompilerStage
target conf = fromMaybe defaultTarget $ explicitTarget conf
  where defaultTarget = Parse   -- this will change as the course proceeds

output :: Configuration -> FilePath
output conf =
  case explicitOutput conf of
    Just path -> path
    _ -> replaceExtension (input conf) $
           case explicitTarget conf of
             Nothing -> ".out"
             Just Scan -> ".scan"
             Just Parse -> ".parse"
             Just Inter -> ".ir"
             Just Assembly -> ".s"
