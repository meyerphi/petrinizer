{-# LANGUAGE TupleSections #-}

module Options
    (InputFormat(..),OutputFormat(..),NetTransformation(..),RefinementType(..),
     ImplicitProperty(..),Options(..),startOptions,options,parseArgs,
     usageInformation)
where

import Control.Applicative ((<$>))
import System.Console.GetOpt
import System.Environment (getArgs)

data InputFormat = PNET | LOLA | TPN | MIST deriving (Show,Read)
data OutputFormat = OutLOLA | OutSARA | OutSPEC | OutDOT deriving (Read)

instance Show OutputFormat where
        show OutLOLA = "LOLA"
        show OutSARA = "SARA"
        show OutSPEC = "SPEC"
        show OutDOT = "DOT"

data NetTransformation = TerminationByReachability
                       | ValidateIdentifiers

data ImplicitProperty = Termination
                      | DeadlockFree | DeadlockFreeUnlessFinal
                      | FinalStateUnreachable
                      | ProperTermination
                      | Safe | Bounded Integer
                      | StructFreeChoice
                      | StructParallel
                      | StructFinalPlace
                      | StructCommunicationFree
                      | TerminalMarkingsUniqueConsensus
                      | TerminalMarkingReachable
                      deriving (Show,Read)

data RefinementType = TrapRefinement | SComponentRefinement | SComponentWithCutRefinement
                    deriving (Show,Read)

data Options = Options { inputFormat :: InputFormat
                       , optVerbosity :: Int
                       , optShowHelp :: Bool
                       , optShowVersion :: Bool
                       , optProperties :: [ImplicitProperty]
                       , optTransformations :: [NetTransformation]
                       , optSimpMethod :: Int
                       , optRefinementType :: Maybe RefinementType
                       , optMinimizeRefinement :: Int
                       , optAuto :: Bool
                       , optSMTAuto :: Bool
                       , optInvariant :: Bool
                       , optBoolConst :: Bool
                       , optOutput :: Maybe String
                       , outputFormat :: OutputFormat
                       , optUseProperties :: Bool
                       , optPrintStructure :: Bool
                       }

startOptions :: Options
startOptions = Options { inputFormat = PNET
                       , optVerbosity = 1
                       , optShowHelp = False
                       , optShowVersion = False
                       , optProperties = []
                       , optTransformations = []
                       , optSimpMethod = 1
                       , optRefinementType = Just SComponentWithCutRefinement
                       , optMinimizeRefinement = 0
                       , optAuto = False
                       , optSMTAuto = True
                       , optInvariant = False
                       , optBoolConst = False
                       , optOutput = Nothing
                       , outputFormat = OutLOLA
                       , optUseProperties = True
                       , optPrintStructure = False
                       }

options :: [ OptDescr (Options -> Either String Options) ]
options =
        [ Option "" ["pnet"]
        (NoArg (\opt -> Right opt { inputFormat = PNET }))
        "Use the pnet input format"

        , Option "" ["lola"]
        (NoArg (\opt -> Right opt { inputFormat = LOLA }))
        "Use the lola input format"

        , Option "" ["tpn"]
        (NoArg (\opt -> Right opt { inputFormat = TPN }))
        "Use the tpn input format"

        , Option "" ["spec"]
        (NoArg (\opt -> Right opt { inputFormat = MIST }))
        "Use the mist input format"

        , Option "" ["structure"]
        (NoArg (\opt -> Right opt { optPrintStructure = True }))
        "Print structural information"

        , Option "" ["validate-identifiers"]
        (NoArg (\opt -> Right opt {
            optTransformations = ValidateIdentifiers : optTransformations opt
          }))
        "Make identifiers valid for lola"

        , Option "" ["termination-by-reachability"]
        (NoArg (\opt -> Right opt {
            optTransformations = TerminationByReachability : optTransformations opt
          }))
        "Prove termination by reducing it to reachability"

        , Option "" ["termination"]
        (NoArg (\opt -> Right opt {
                   optProperties = Termination : optProperties opt
               }))
        "Prove that the net is terminating"

        , Option "" ["proper-termination"]
        (NoArg (\opt -> Right opt {
                   optProperties = ProperTermination : optProperties opt
               }))
        "Prove termination in the final marking"

        , Option "" ["deadlock-free"]
        (NoArg (\opt -> Right opt {
                   optProperties = DeadlockFree : optProperties opt
               }))
        "Prove that the net is deadlock-free"

        , Option "" ["deadlock-free-unless-final"]
        (NoArg (\opt -> Right opt {
                   optProperties = DeadlockFreeUnlessFinal : optProperties opt
               }))
        ("Prove that the net is deadlock-free\n" ++
         "  unless it is in the final marking")

        , Option "" ["final-state-unreachable"]
        (NoArg (\opt -> Right opt {
                   optProperties = FinalStateUnreachable : optProperties opt
               }))
        "Prove that the final state is unreachable"

        , Option "" ["safe"]
        (NoArg (\opt -> Right opt {
                   optProperties = Safe : optProperties opt
               }))
        "Prove that the net is safe, i.e. 1-bounded"

        , Option "" ["bounded"]
        (ReqArg (\arg opt -> case reads arg of
                    [(k, "")] -> Right opt {
                           optProperties = Bounded k : optProperties opt }
                    _ -> Left ("invalid argument for k-bounded option: " ++ arg)
                )
                "K")
        "Prove that the net is K-bounded"

        , Option "" ["free-choice"]
        (NoArg (\opt -> Right opt {
                   optProperties = StructFreeChoice : optProperties opt
               }))
        "Prove that the net is free-choice"

        , Option "" ["parallel"]
        (NoArg (\opt -> Right opt {
                   optProperties = StructParallel : optProperties opt
               }))
        "Prove that the net has non-trivial parallellism"

        , Option "" ["final-place"]
        (NoArg (\opt -> Right opt {
                   optProperties = StructFinalPlace : optProperties opt
               }))
        "Prove that there is only one needed final place"

        , Option "" ["communication-free"]
        (NoArg (\opt -> Right opt {
                   optProperties = StructCommunicationFree : optProperties opt
               }))
        "Prove that the net is communication-free"

        , Option "" ["terminal-markings-unique-consensus"]
        (NoArg (\opt -> Right opt {
                   optProperties = TerminalMarkingsUniqueConsensus : optProperties opt
               }))
        "Prove that terminal markings have a unique consensus"

        , Option "" ["terminal-marking-reachable"]
        (NoArg (\opt -> Right opt {
                   optProperties = TerminalMarkingReachable : optProperties opt
               }))
        "Prove that a terminal marking is reachable"

        , Option "i" ["invariant"]
        (NoArg (\opt -> Right opt { optInvariant = True }))
        "Generate an invariant"

        , Option "" ["bool-const"]
        (NoArg (\opt -> Right opt { optBoolConst = True }))
        ("Use boolean constraints instead of integer ones\n" ++
         "  for transition invariant")

        , Option "r" ["refinement"]
        (ReqArg (\arg opt -> case reads arg :: [(Int, String)] of
                    [(0, "")] -> Right opt { optRefinementType = Nothing }
                    [(1, "")] -> Right opt { optRefinementType = Just SComponentWithCutRefinement }
                    [(2, "")] -> Right opt { optRefinementType = Just SComponentRefinement }
                    [(3, "")] -> Right opt { optRefinementType = Just TrapRefinement }
                    _ -> Left ("invalid argument for refinement method: " ++ arg)
                )
                "METHOD")
        ("Refine with METHOD (0=none, 1=SCompCut+Traps,\n" ++
         "  2=SComp+Traps, 3=Traps)")

        , Option "o" ["output"]
        (ReqArg (\arg opt -> Right opt {
                        optOutput = Just arg
                })
                "FILE")
        "Write net and properties to FILE"

        , Option "" ["out-lola"]
        (NoArg (\opt -> Right opt { outputFormat = OutLOLA }))
        "Use the lola output format"

        , Option "" ["out-sara"]
        (NoArg (\opt -> Right opt { outputFormat = OutSARA }))
        "Use the sara output format"

        , Option "" ["out-spec"]
        (NoArg (\opt -> Right opt { outputFormat = OutSPEC }))
        "Use the spec output format"

        , Option "" ["out-dot"]
        (NoArg (\opt -> Right opt { outputFormat = OutDOT }))
        "Use the dot output format"

        , Option "" ["no-given-properties"]
        (NoArg (\opt -> Right opt {
                   optUseProperties = False
               }))
        "Do not use the properties given in the input file"

        , Option "s" ["simp"]
        (ReqArg (\arg opt -> case reads arg of
                    [(i, "")] -> Right opt { optSimpMethod = i }
                    _ -> Left ("invalid argument for simplification method: " ++ arg)
                )
                "METHOD")
        "Simply formula with method METHOD (0-2)"

        , Option "" ["simp-1"]
        (NoArg (\opt -> Right opt {
                   optSimpMethod = 1
               }))
        "Use simplification level 1 for invariant generation"

        , Option "" ["simp-2"]
        (NoArg (\opt -> Right opt {
                   optSimpMethod = 2
               }))
        "Use simplification level 2 for invariant generation"

        , Option "m" ["minimize"]
        (ReqArg (\arg opt -> case reads arg of
                        [(i, "")] -> Right opt { optMinimizeRefinement = i }
                        _ -> Left ("invalid argument for minimization method: " ++ arg)
                )
                "METHOD")
        "Minimize size of refinement structure by method METHOD (1-4)"

        , Option "" ["auto"]
        (NoArg (\opt -> Right opt { optAuto = True }))
        "Automatically find best refinement, minimization and simplification method"

        , Option "" ["smt-disable-auto-config"]
        (NoArg (\opt -> Right opt { optSMTAuto = False }))
        "Disable automatic configuration of the SMT solver"

        , Option "v" ["verbose"]
        (NoArg (\opt -> Right opt { optVerbosity = optVerbosity opt + 1 }))
        "Increase verbosity (may be specified more than once)"

        , Option "q" ["quiet"]
        (NoArg (\opt -> Right opt { optVerbosity = optVerbosity opt - 1 }))
        "Decrease verbosity (may be specified more than once)"

        , Option "V" ["version"]
        (NoArg (\opt -> Right opt { optShowVersion = True }))
        "Show version"

        , Option "h" ["help"]
        (NoArg (\opt -> Right opt { optShowHelp = True }))
        "Show help"
        ]

parseArgs :: IO (Either String (Options, [String]))
parseArgs = do
        args <- getArgs
        case getOpt Permute options args of
            (actions, files, []) ->
                return $ (,files) <$> foldl (>>=) (return startOptions) actions
            (_, _, errs) -> return $ Left $ concat errs

usageInformation :: String
usageInformation = usageInfo "SLAPnet" options
