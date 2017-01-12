module Parser.TPN
    (parseContent)
where

import Control.Applicative ((*>))
import Control.Arrow ((&&&))
import Text.Parsec
import Text.Parsec.Language (LanguageDef, emptyDef)
import qualified Text.Parsec.Token as Token
import Data.List (group,sort,genericLength)

import Parser
import PetriNet (PetriNet,makePetriNetWithTransFromStrings)
import Property

languageDef :: LanguageDef ()
languageDef =
        emptyDef {
                 Token.commentStart    = "",
                 Token.commentEnd      = "",
                 Token.commentLine     = "--",
                 Token.identStart      = letter <|> char '_',
                 Token.identLetter     = alphaNum <|> char '_',
                 Token.reservedNames   = ["place", "trans", "init",
                                          "in", "out"],
                 Token.reservedOpNames = ["~"]
                 }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef

identifier :: Parser String
identifier = Token.identifier lexer -- parses an identifier
stringLiteral :: Parser String
stringLiteral = Token.stringLiteral lexer -- parses a string literal
reserved :: String -> Parser ()
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer -- parses an operator
natural :: Parser Integer
natural    = Token.natural    lexer -- parses a natural number
semi :: Parser String
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer -- parses whitespace


ident :: Parser String
ident = (identifier <|> stringLiteral) <?> "identifier"

place :: Parser (String, Maybe Integer)
place = do
        reserved "place"
        p <- ident
        initial <- optionMaybe (reserved "init" *> natural)
        _ <- semi
        return (p, initial)

adjacencyList :: Parser [(String, Integer)]
adjacencyList = do
        xs <- many1 ident
        return $ map (head &&& genericLength) $ group $ sort xs

transition :: Parser (String, ([(String, Integer)], [(String, Integer)]))
transition = do
        reserved "trans"
        t <- ident
        _ <- optionMaybe (reservedOp "~" *> ident)
        input <- option [] (reserved "in" *> adjacencyList)
        output <- option [] (reserved "out" *> adjacencyList)
        _ <- semi
        return (t, (input, output))

petriNet :: Parser PetriNet
petriNet = do
        ps <- many place
        ts <- many transition
        let places = [ p | (p,_) <- ps ]
            initial = [ (p,i) | (p,Just i) <- ps ]
        return $ makePetriNetWithTransFromStrings "" places ts initial [] [] [] [] []

parseContent :: Parser (PetriNet,[Property])
parseContent = do
        whiteSpace
        net <- petriNet
        eof
        return (net, [])
