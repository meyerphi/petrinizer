module Parser.LOLA
    (module Parser.LOLAFormula,
     parseContent)
where

import Control.Applicative ((*>),(<*))
import Text.Parsec
import Text.Parsec.Language (LanguageDef, emptyDef)
import qualified Text.Parsec.Token as Token

import Parser
import Parser.LOLAFormula
import PetriNet (PetriNet,makePetriNetWithTransFromStrings)
import Property

languageDef :: LanguageDef ()
languageDef =
        emptyDef {
                 Token.commentStart    = "{",
                 Token.commentEnd      = "}",
                 Token.commentLine     = "",
                 Token.identStart      = noneOf ",;:(){}\t \n\r",
                 Token.identLetter     = noneOf ",;:(){}\t \n\r",
                 Token.reservedNames   = ["PLACE", "MARKING", "SAFE",
                                          "TRANSITION", "CONSUME", "PRODUCE",
                                          "STRONG", "WEAK", "FAIR"],
                 Token.reservedOpNames = []
                 }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDef

identifier :: Parser String
identifier = Token.identifier lexer -- parses an identifier
reserved :: String -> Parser ()
reserved   = Token.reserved   lexer -- parses a reserved name
integer :: Parser Integer
integer    = Token.integer    lexer -- parses an integer
colon :: Parser String
colon      = Token.colon      lexer -- parses a colon
semi :: Parser String
semi       = Token.semi       lexer -- parses a semicolon
commaSep1 :: Parser a -> Parser [a]
commaSep1  = Token.commaSep1  lexer -- parses a comma separated list
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer -- parses whitespace


ident :: Parser String
ident = (identifier <|> fmap show integer) <?> "identifier"

net :: Parser PetriNet
net = do
        reserved "PLACE"
        ps <- placeLists
        reserved "MARKING"
        initial <- option [] markingList
        _ <- semi
        ts <- many1 transition
        return $ makePetriNetWithTransFromStrings "" ps ts initial [] [] [] [] []

placeLists :: Parser [String]
placeLists =
        fmap concat (many1 (do
            _ <- optionMaybe (reserved "SAFE" *> option 1 integer <* colon)
            ps <- placeList
            _ <- semi
            return ps
        ))

placeList :: Parser [String]
placeList = commaSep1 ident

markingList :: Parser [(String, Integer)]
markingList = commaSep1 marking

marking :: Parser (String, Integer)
marking = do
        s <- ident
        i <- option 1 (colon *> integer)
        return (s, i)

transition :: Parser (String, ([(String, Integer)], [(String, Integer)]))
transition = do
        reserved "TRANSITION"
        t <- ident
        _ <- optionMaybe ((reserved "STRONG" <|> reserved "WEAK") <*
                          reserved "FAIR")
        reserved "CONSUME"
        input <- option [] arcList
        _ <- semi
        reserved "PRODUCE"
        output <- option [] arcList
        _ <- semi
        return (t, (input, output))

arcList :: Parser [(String, Integer)]
arcList = commaSep1 arc

arc :: Parser (String, Integer)
arc = do
        x <- ident
        w <- option 1 (colon *> integer)
        return (x, w)

parseContent :: Parser (PetriNet,[Property])
parseContent = do
        whiteSpace
        n <- net
        eof
        return (n, [])
