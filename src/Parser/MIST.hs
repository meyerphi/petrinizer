module Parser.MIST
    (parseContent)
where

import Control.Applicative ((<$>),(*>),(<*),(<*>))
import Control.Monad (when)
import Data.List (sortBy, groupBy)
import Data.Function (on)
import Data.Ord (comparing)
import Text.Parsec
import Text.Parsec.Language (LanguageDef, emptyDef)
import qualified Text.Parsec.Token as Token

import Parser
import PetriNet (PetriNet,makePetriNetWithTransFromStrings,Place(..))
import Property

languageDef :: LanguageDef ()
languageDef =
        emptyDef {
                 Token.commentStart    = "",
                 Token.commentEnd      = "",
                 Token.commentLine     = "#",
                 Token.identStart      = letter <|> char '_',
                 Token.identLetter     = alphaNum <|> oneOf "'_",
                 Token.reservedNames   = ["vars", "rules", "init",
                                          "target", "invariants"],
                 Token.reservedOpNames = ["->", "+", "-", "=", ">="]
                 }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef

identifier :: Parser String
identifier = Token.identifier lexer -- parses an identifier
reserved :: String -> Parser ()
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer -- parses an operator
integer :: Parser Integer
integer    = Token.integer    lexer -- parses an integer
semi :: Parser String
semi       = Token.semi       lexer -- parses a semicolon
commaSep :: Parser a -> Parser [a]
commaSep   = Token.commaSep   lexer -- parses a comma separated list
commaSep1 :: Parser a -> Parser [a]
commaSep1  = Token.commaSep1  lexer -- parses a comma separated list
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer -- parses whitespace


net :: Parser PetriNet
net = do
        reserved "vars"
        ps <- many1 identifier
        reserved "rules"
        ts <- transitions
        reserved "init"
        (is,initTrans) <- initial
        return $ makePetriNetWithTransFromStrings "" ps (initTrans ++ ts) is
                 (map fst initTrans) [] []

prop :: Parser Property
prop = do
        reserved "target"
        ineqs <- many1 (commaSep1 ineq)
        _ <- optionMaybe (reserved "invariants" *> invariants)
        return $ Property "" $ Safety $
                    foldl1 (:|:) $ map (foldl1 (:&:)) ineqs

ineq :: Parser (Formula Place)
ineq = do
        x <- identifier
        reservedOp ">="
        c <- integer
        return $ LinearInequation (Var (Place x)) Ge (Const c)

transitions :: Parser [(String, ([(String, Integer)], [(String, Integer)]))]
transitions = do
        ts <- many1 transition
        return $ map (\(i,(l,r)) -> ("'t" ++ show i,(l,r)))
                        ([(1::Integer)..] `zip` ts)

transition :: Parser ([(String, Integer)], [(String, Integer)])
transition = do
        lhs <- commaSep ((,) <$> identifier <* reservedOp ">=" <*> integer)
        reservedOp "->"
        rhs <- commaSep transitionAssignment
        let rhs' = map (\xs -> (fst (head xs), sum (map snd xs))) $
                   groupBy ((==) `on` fst) $
                   sortBy (comparing fst) $
                   lhs ++ rhs
        _ <- semi
        return (lhs, rhs')

transitionAssignment :: Parser (String, Integer)
transitionAssignment = do
        i1 <- identifier
        reservedOp "="
        i2 <- identifier
        when (i1 /= i2 ++ "'")
            (error ("identifiers not equal: " ++ i1 ++ " /= " ++ i2))
        fac <- (reservedOp "-" *> return (-1)) <|> (reservedOp "+" *> return 1)
        n <- integer
        return (i2,fac*n)

initial :: Parser ([(String, Integer)],
                  [(String, ([(String, Integer)], [(String, Integer)]))])
initial = do
        xs <- commaSep1 initState
        let inits = [(x,i) | (x,i,_) <- xs]
        let covered = [x | (x,_,True) <- xs]
        let initTrans = map (\(i,x) -> ("'init" ++ show i, ([], [(x,1)])))
                            ([(1::Integer)..] `zip` covered)
        return (inits, initTrans)

initState :: Parser (String, Integer, Bool)
initState = do
        s <- identifier
        cover <- reservedOp "=" *> return False <|>
                reservedOp ">=" *> return True
        i <- integer
        return (s,i,cover)

invariants :: Parser [[(String, Integer)]]
invariants = many1 (commaSep1 ((,) <$> identifier <* reservedOp "=" <*> integer))

parseContent :: Parser (PetriNet,[Property])
parseContent = do
        whiteSpace
        n <- net
        p <- prop
        eof
        return (n, [p])
