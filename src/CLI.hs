{- CLI -- command-line options
Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>

This file is a part of decafc.

decafc is free software: you can redistribute it and/or modify it under the
terms of the MIT (X11) License as described in the LICENSE file.

decafc is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the X11 license for more details. -}
module CLI (generateUsage, getConfiguration) where

import Control.Applicative ((<$>))
import Control.Monad (foldM)
import Data.List.Split (wordsBy)
import System.Console.GetOpt
import System.Environment (getArgs, getProgName)
import Text.Printf (printf)

import Configuration
import Configuration.Types


--------------------------------- FlagAction ----------------------------------

-- I'll describe the behavior of each flag in terms of a 'FlagAction':
type FlagAction = Configuration -> Either String Configuration

{- Later, I'll 'foldM' over a list of FlagActions to apply them to a
configuration type.  If a FlagAction fails (e.g., because it was unable to
parse an argument), it'll return a 'Left', in which case the error will be
detectable at the end of the fold.  (Of course, I won't be able to recover from
command-line errors, but this seems reasonable behavior for a compiler. -}


------------------------------- Available flags -------------------------------

generateUsage :: IO String
generateUsage = do
  firstLine <- generateSummary
  return $ unlines [ firstLine
                   , usageInfo "Summary of options:" options
                   , "Long description of options:"
                   , init longDescription -- drop trailing newline
                   ]

{- The rest of this section is organized in the order of the lines in the usage
message. -}

generateSummary :: IO String
generateSummary =
  printf "%s [options] <filename>"
         <$> getProgName

options :: [OptDescr FlagAction]
options = [ Option ['t'] ["target"]
                   (ReqArg (\stage -> \conf -> do
                                         parsedStage <- readStage stage
                                         return $ conf { explicitTarget = Just parsedStage })
                           "<stage>")
                   "compile to the given stage"
          , Option ['o'] ["output"]
                   (ReqArg (\outfile -> \conf ->
                                         Right $ conf { outputFileName = Just outfile })
                           "<outfile>")
                   "write output to <outfile>"
          , Option ['O'] ["opt"]
                   (ReqArg (\optSpec -> \conf -> do
                                           parsedOptSpec <- readOptimizationSpec optSpec
                                           return $ conf { opt = parsedOptSpec })
                           "<(opt|-opt|all)...>")
                   "perform the listed optimizations"
          , Option ['d'] ["debug"]
                   (NoArg (\conf -> Right $ conf { debug = True }))
                   "print debugging information"
          ]

longDescription :: String
longDescription = unlines [ "  -t <stage>          <stage> is one of \"scan\", \"parse\", \"inter\", or \"assembly\"."
                          , "  --target=<stage>    Compilation will proceed to the given stage and halt there."
                          , "  "
                          , "  -d                  Print debugging information.  If this option is not given,"
                          , "  --debug             then there will be no output to the screen on successful"
                          , "  "
                          , "  -O <optspec>        Perform the listed optimizations.  <optspec> is a comma-"
                          , "  --opt=<optspec>     separated list of optimization names, or the special symbol"
                          , "                      \"all\", meaning all possible optimizations.  You may"
                          , "                      explicitly disable an optimization by prefixing its name"
                          , "                      '-'.  As an example, \"hoistLoop,-unrollLoops\" will enable"
                          , "                      hoisting of loop invariant code but will disable loop"
                          , "                      unrolling."
                          , "  "
                          , "  -o <outfile>        Write output to <outfile>.  If this option is not given,"
                          , "  --output=<outfile>  output will be written to standard output."
                          ]


---------------------------- Reading option specs -----------------------------

readStage :: String -> Either String CompilerStage
readStage stageString =
  case reads stageString of
    [(stage, "")] -> Right stage
    _ -> Left $ printf "unknown stage `%s'\n" stageString

readOptimizationSpec :: String -> Either String OptimizationSpecification
readOptimizationSpec optString =
  let opts = wordsBy (==',') optString in
  if "all" `elem` opts
  then Right All
  else Right $ Some $ for opts $ \optSpec -> case optSpec of
                                               ('-':optName) -> Disable optName
                                               optName -> Enable optName
  where for = flip map


------------------------------ Main entry points ------------------------------

{-| Parses command-line options, returning a 'Configuration' describing the
behavior of the compiler. -}
getConfiguration :: IO (Either String Configuration)
getConfiguration = do
  -- Fetch the arguments and process them.
  args <- getArgs
  -- return $ do
  let maybeSelectedOptions = do
        let (flagActions, nonOptions, errors) = getOpt Permute options args
        -- If there were any errors, notify the monad.
        mapM_ Left errors
        {- Construct the options struct by applying the 'flagActions' to the
        default configuration. -}
        selectedOptions <- foldM (flip id) defaultConfiguration flagActions
        -- What file are we reading?
        inputFileName <-
          maybeToEither "no input file specified\n" $ headMay nonOptions
        Right $ selectedOptions { input = inputFileName }
  case maybeSelectedOptions of
    Left errorMessage -> do
      usage <- init <$> generateUsage -- drop trailing newline
      return $ Left $ init $ unlines [errorMessage, usage]
    Right selectedOptions -> return $ Right selectedOptions

  where maybeToEither _ (Just a) = Right a
        maybeToEither msg Nothing = Left msg
        headMay [] = Nothing
        headMay (x:_) = Just x
