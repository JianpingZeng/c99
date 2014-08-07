%language "Java"

%define package "c99.parser"
%code imports {
import c99.Constant;
import c99.CompilerOptions;
import c99.IErrorReporter;
import c99.parser.ast.Ast;
import c99.Types.*;
}
%define public
%define parser_class_name {CParser}
%define extends {ParserActions}

%parse-param { CompilerOptions opts_ }
%parse-param { IErrorReporter reporter_ }
%parse-param { SymTable symTab_ }
%code init {
  super.init( opts_, reporter_, symTab_ );
  pushScope(Scope.Kind.FILE);
}

%define parse.error verbose

%locations

%destructor { popScope( (Scope)$$ ); } <Scope>

%token<Symbol> IDENT  "identifier"
%token<Decl> TYPENAME "typedef name"
%token<Constant.IntC> INT_NUMBER  "integer number"
%token<Constant.RealC> REAL_NUMBER "real number"
%token<Constant.IntC> CHAR_CONST   "character literal"
%token WIDE_CHAR_CONST "wide character literal"
%token<byte[]> STRING_CONST    "string literal"
%token WIDE_STRING_CONST  "wide string literal"

%token L_BRACKET   "["
%token R_BRACKET   "]"
%token L_PAREN   "("
%token R_PAREN   ")"
%token L_CURLY   "{"
%token R_CURLY   "}"
%token FULLSTOP   "."
%token MINUS_GREATER   "->"

%token PLUS_PLUS   "++"
%token MINUS_MINUS   "--"
%token<Code> AMPERSAND   "&"
%token<Code> ASTERISK   "*"
%token<Code> PLUS   "+"
%token<Code> MINUS   "-"
%token<Code> TILDE   "~"
%token<Code> BANG   "!"

%token SLASH   "/"
%token PERCENT   "%"
%token LESS_LESS   "<<"
%token GREATER_GREATER   ">>"
%token LESS   "<"
%token GREATER   ">"
%token LESS_EQUALS   "<="
%token GREATER_EQUALS   ">="
%token EQUALS_EQUALS   "=="
%token BANG_EQUALS   "!="
%token CARET   "^"
%token VERTICAL   "|"
%token AMPERSAND_AMPERSAND   "&&"
%token VERTICAL_VERTICAL   "||"

%token QUESTION   "?"
%token COLON   ":"
%token SEMICOLON   ";"
%token<Code> ELLIPSIS   "..."

%token EQUALS   "="
%token ASTERISK_EQUALS   "*="
%token SLASH_EQUALS   "/="
%token PERCENT_EQUALS   "%="
%token PLUS_EQUALS   "+="
%token MINUS_EQUALS   "-="
%token LESS_LESS_EQUALS   "<<="
%token GREATER_GREATER_EQUALS   ">>="
%token AMPERSAND_EQUALS   "&="
%token CARET_EQUALS   "^="
%token VERTICAL_EQUALS   "|="

%token COMMA   ","


%token<Code> AUTO   "auto"
%token BREAK   "break"
%token CASE   "case"
%token<Code> CHAR   "char"
%token<Code> CONST   "const"
%token CONTINUE   "continue"
%token DEFAULT   "default"
%token DO   "do"
%token<Code> DOUBLE   "double"
%token ELSE   "else"
%token<Code> ENUM   "enum"
%token<Code> EXTERN   "extern"
%token<Code> FLOAT   "float"
%token FOR   "for"
%token GOTO   "goto"
%token IF   "if"
%token<Code> INLINE   "INLINE"
%token<Code> INT   "int"
%token<Code> LONG   "long"
%token<Code> REGISTER   "register"
%token<Code> RESTRICT   "restrict"
%token RETURN   "return"
%token<Code> SHORT   "short"
%token<Code> SIGNED   "signed"
%token SIZEOF   "sizeof"
%token<Code> STATIC   "static"
%token<Code> STRUCT   "struct"
%token SWITCH   "switch"
%token<Code> TYPEDEF   "typedef"
%token<Code> UNION   "union"
%token<Code> UNSIGNED   "unsigned"
%token<Code> VOID   "void"
%token<Code> VOLATILE   "volatile"
%token WHILE   "while"
%token<Code> _ALIGNAS   "_Alignas"
%token _ALIGNOF   "_Alignof"
%token<Code> _ATOMIC   "_Atomic"
%token<Code> _BOOL   "_Bool"
%token<Code> _COMPLEX   "_Complex"
%token _GENERIC   "_Generic"
%token<Code> _IMAGINARY   "_Imaginary"
%token<Code> _NORETURN   "_Noreturn"
%token<Code> _STATIC_ASSERT   "_Static_assert"
%token<Code> _THREAD_LOCAL   "_Thread_local"

// Set precedences to avoid IF-ELSE `shift'/reduce conflict
%precedence IF
%precedence ELSE

%type<Ast> string-literal
%type<Ast> constant
%type<Ast> enumerator-list
%type<Ast> enumerator
%type<Ast> initializer
%type<Ast> initializer-list
%type<Ast> designation designation_opt
%type<Ast> designator-list
%type<Ast> designator
%type<Ast> static_assert-declaration

%type<Ast> statement
%type<Ast> labeled-statement
%type<Ast> compound-statement
%type<Ast> block-item-list block-item-list_opt
%type<Ast> expression-statement
%type<Ast> selection-statement
%type<Ast> iteration-statement
%type<Ast> jump-statement

%type<Ast> primary-expression
%type<Ast> generic-selection
%type<Ast> generic-assoc-list
%type<Ast> generic-association
%type<Ast> postfix-expression
%type<Ast> argument-expression-list
%type<Ast> argument-expression-list_opt
%type<Ast> unary-expression
%type<String> unary-operator
%type<Ast> cast-expression
%type<Ast> multiplicative-expression
%type<Ast> additive-expression
%type<Ast> shift-expression
%type<Ast> relational-expression
%type<Ast> equality-expression
%type<Ast> AND-expression
%type<Ast> exclusive-OR-expression
%type<Ast> inclusive-OR-expression
%type<Ast> logical-AND-expression
%type<Ast> logical-OR-expression
%type<Ast> conditional-expression
%type<Ast> assignment-expression assignment-expression_opt
%type<String> assignment-operator
%type<Ast> expression expression_opt
%type<Ast> constant-expression

%expect 3
%start translation-unit

start_grammar
%%

rule(<Symbol>,identifier):
    IDENT
  ;

rule(<Symbol>,any-identifier,opt):
    TYPENAME    { $$ = $TYPENAME.symbol; }
  | IDENT
  ;

string-literal:
    STRING_CONST                        { $$ = stringLiteral( $STRING_CONST ); }
  | string-literal STRING_CONST         { $$ = stringLiteral( $1, $STRING_CONST ); }
  ;

constant:
    INT_NUMBER                          { $$ = constant($1,@1); }
  | REAL_NUMBER                         { $$ = constant($1,@1); }
  | CHAR_CONST                          { $$ = constant($1,@1); }
/*  | enumeration-constant*/
  ;

// A.2.4 External definitions
//

// (6.9)
translation-unit:
    %empty
  | translation-unit external-declaration
  ;

// (6.9)
external-declaration:
    function-definition
  | declaration
  ;

// (6.9.1)
function-definition:
    specified-func-declarator compound-statement
  | specified-func-declarator PushParamScope declaration-list {} compound-statement
        { popScope($PushParamScope); FIXME(); }
  ;

rule(<Ast>,specified-func-declarator):
    declaration-specifiers-nots[ds] func-declarator-notyp[decl]  { $$ = declare($decl,$ds,true); }
  | declaration-specifiers-ts[ds]   func-declarator[decl]        { $$ = declare($decl,$ds,true); }
  ;

// (6.9.1)
declaration-list:
    declaration
  | declaration-list declaration
  ;

// A.2.2. Declarations
//

// The conflict is as follows:
//    first-part TYPENAME
// Is TYPENAME part of the declaration specifiers, or is it the identifier that is being re-defined?
//
// The rule is that if we have encountered a <type-specifier> or another TYPENAME in "first-part", then this
// TYPENAME is just an identifier. If we haven't, then this TYPENAME is part of the type specifier.
//
// "first-part-without-TYPENAME-and-type-specifier" TYPENAME-as-type
// "first-part-with-TYPENAME-or-type-specifier" TYPENAME-as-ident

// (6.7)
//declaration:
//    declaration-specifiers init-declarator-list_opt ";"
//  | static_assert-declaration
//  ;

// (6.7)
//declaration-specifiers:
//    storage-class-specifier declaration-specifiers_opt
//  | type-specifier declaration-specifiers_opt
//  | type-qualifier declaration-specifiers_opt
//  | function-specifier declaration-specifiers_opt
//  | alignment-specifier declaration-specifiers_opt
//  ;

//declaration-specifiers_opt:
//    %empty | declaration-specifiers
//  ;

declaration:
    static_assert-declaration
  | declaration-specifiers-nots init-declarator-list-notyp_opt ";"
  | declaration-specifiers-ts   init-declarator-list_opt ";"
  ;

rule(<DeclSpec>,declaration-specifiers-nots):
    _declaration-specifiers-nots { $$ = declSpec(@1,$1); }
  ;

rule(<DeclSpec>,declaration-specifiers-ts):
    _declaration-specifiers-ts   { $$ = declSpec(@1,$1); }
  ;

rule(<SpecNode>,_declaration-specifiers-nots):
    specifier-nots
  | specifier-nots _declaration-specifiers-nots  { $$ = append( $1, $2 ); }
  ;

rule(<SpecNode>,_declaration-specifiers-ts):
    type-specifier declaration-specifiers-ts-rest  { $$ = append( $1, $2 ); }
  | specifier-nots _declaration-specifiers-ts       { $$ = append( $1, $2 ); }
  ;

rule(<SpecNode>,declaration-specifiers-ts-rest):
    %empty                                               { $$ = null; }
  | type-specifier-notyp declaration-specifiers-ts-rest  { $$ = append( $1, $2 ); }
  | specifier-nots declaration-specifiers-ts-rest        { $$ = append( $1, $2 ); }
  ;

rule(<SpecNode>,specifier-nots):
    storage-class-specifier
  | type-qualifier
  | function-specifier
  | alignment-specifier
  ;

// (6.7)
rule(<Ast>,init-declarator-list,opt,declaration-specifiers):
    init-declarator                                 { $$ = ast("init-declarator-list", $[init-declarator]); }
  | init-declarator-list "," _PUSH0 init-declarator  { $$ = astAppend($1, $[init-declarator]); }
  ;

rule(<Ast>,init-declarator-list-notyp,opt,declaration-specifiers):
    init-declarator-notyp                                { $$ = ast("init-declarator-list", $[init-declarator-notyp]); }
  | init-declarator-list-notyp "," _PUSH0 init-declarator { $$ = astAppend($1, $[init-declarator]); }
  ;

// (6.7)
rule(<Ast>,init-declarator,,declaration-specifiers):
    declarator[decl]                  { $$ = FIXME(); declare($decl,$<DeclSpec>0,false); }
  | declarator[decl] "=" initializer  { $$ = FIXME(); declare($decl,$<DeclSpec>0,true); }
  ;

rule(<Ast>,init-declarator-notyp,,declaration-specifiers):
    declarator-notyp[decl]                  { $$ = FIXME(); declare($decl,$<DeclSpec>0,false); }
  | declarator-notyp[decl] "=" initializer  { $$ = FIXME(); declare($decl,$<DeclSpec>0,true); }
  ;

// (6.7.1)
rule(<SpecNode>,storage-class-specifier):
    TYPEDEF                    { $$ = spec(@1,$1); }
  | EXTERN                     { $$ = spec(@1,$1); }
  | STATIC                     { $$ = spec(@1,$1); }
  | _THREAD_LOCAL              { $$ = spec(@1,$1); }
  | AUTO                       { $$ = spec(@1,$1); }
  | REGISTER                   { $$ = spec(@1,$1); }
  ;

// (6.7.2)
rule(<SpecNode>,type-specifier):
    type-specifier-notyp
  | TYPENAME                    { $$ = specTypename(@1,$1); }
  ;

rule(<SpecNode>,type-specifier-notyp):
    VOID                        { $$ = spec(@1,$1); }
  | CHAR                        { $$ = spec(@1,$1); }
  | SHORT                       { $$ = spec(@1,$1); }
  | INT                         { $$ = spec(@1,$1); }
  | LONG                        { $$ = spec(@1,$1); }
  | FLOAT                       { $$ = spec(@1,$1); }
  | DOUBLE                      { $$ = spec(@1,$1); }
  | SIGNED                      { $$ = spec(@1,$1); }
  | UNSIGNED                    { $$ = spec(@1,$1); }
  | _BOOL                       { $$ = spec(@1,$1); }
  | _COMPLEX                    { $$ = spec(@1,$1); }
  | _IMAGINARY                  { $$ = spec(@1,$1); }
  | atomic-type-specifier
  | struct-or-union-specifier
  | enum-specifier
  ;

// (6.7.2.1)
rule(<SpecNode>,struct-or-union-specifier):
    struct-or-union any-identifier_opt "{" PushAggScope struct-declaration-list "}"
      { $$ = declareAgg(@[struct-or-union], $[struct-or-union], @[any-identifier_opt], $[any-identifier_opt], popScope($PushAggScope)); }
  | struct-or-union any-identifier
      { $$ = specAgg(@[struct-or-union], $[struct-or-union], @[any-identifier], $[any-identifier]); }
  ;

// (6.7.2.1)
rule(<Code>,struct-or-union):
    STRUCT
  | UNION
  ;

// (6.7.2.1)
struct-declaration-list:
    struct-declaration
  | struct-declaration-list struct-declaration
  ;

// (6.7.2.1)
struct-declaration:
    static_assert-declaration
  | declaration-specifiers-nots struct-declarator-list-notyp_opt ";"
  | declaration-specifiers-ts   struct-declarator-list_opt ";"
  ;

// (6.7.2.1)
rule(<SpecNode>,specifier-qualifier-list):
    specifier-or-qualifier
  | specifier-qualifier-list specifier-or-qualifier     { $$ = append($1,$2); }
  ;

rule(<SpecNode>,specifier-or-qualifier):
    type-specifier
  | type-qualifier
  ;

// (6.7.2.1)
rule(,struct-declarator-list,optn):
    struct-declarator
  | struct-declarator-list "," _PUSH0 struct-declarator
  ;

rule(,struct-declarator-list-notyp,optn):
    struct-declarator-notyp
  | struct-declarator-list-notyp "," _PUSH0 struct-declarator
  ;

// (6.7.2.1)
struct-declarator:
    declarator[decl]                              { declare($decl,$<DeclSpec>0); }
  | declarator_opt ":" constant-expression        { FIXME(); }
  ;

struct-declarator-notyp:
    declarator-notyp[decl]                         { declare($decl,$<DeclSpec>0); }
  | declarator-notyp_opt ":" constant-expression   { FIXME(); }
  ;

// (6.7.2.2)
rule(<SpecNode>,enum-specifier):
    ENUM any-identifier_opt "{" enumerator-list "}"             { FIXME(); }
  | ENUM any-identifier_opt "{" enumerator-list "," "}"         { FIXME(); }
  | ENUM any-identifier                                         { FIXME(); }  
  ;

// (6.7.2.2)
enumerator-list:
    enumerator                       { $$ = ast( "enumerator-list", $1 ); }
  | enumerator-list "," enumerator   { $$ = astAppend( $1, $3 ); }
  ;

// (6.7.2.2)
enumerator:
    enumeration-constant                          { FIXME(); }
  | enumeration-constant "=" constant-expression  { FIXME(); }
  ;

enumeration-constant:
    any-identifier
  ;

// (6.7.2.4)
rule(<SpecNode>,atomic-type-specifier):
    _ATOMIC "(" type-name ")"  { FIXME(); }
  ;

// (6.7.3)
rule(<SpecNode>,type-qualifier):
    CONST       { $$ = spec(@1,$1); }
  | RESTRICT    { $$ = spec(@1,$1); }
  | VOLATILE    { $$ = spec(@1,$1); }
  | _ATOMIC     { $$ = spec(@1,$1); }
  ;

// (6.7.4)
rule(<SpecNode>,function-specifier):
    INLINE      { $$ = spec(@1,$1); }
  | _NORETURN   { $$ = spec(@1,$1); }
  ;

// (6.7.5)
rule(<SpecNode>,alignment-specifier):
    _ALIGNAS "(" type-name ")"                  { FIXME(); }
  | _ALIGNAS "(" constant-expression ")"        { FIXME(); }
  ;

// (6.7.6)
rule(<Declarator>,declarator):
    nofunc-declarator
  | func-declarator
  ;
rule(<Declarator>,declarator_opt):
    declarator
  | %empty                              { $$ = abstractDeclarator(yyloc); }
  ;


rule(<Declarator>,declarator-notyp):
    nofunc-declarator-notyp
  | func-declarator-notyp
  ;
rule(<Declarator>,declarator-notyp_opt):
    declarator-notyp
  | %empty                              { $$ = abstractDeclarator(yyloc); }
  ;

rule(<Declarator>,nofunc-declarator):
    pointer_opt[ptr] direct-nofunc-declarator[decl]  { $$ = $decl.append($ptr); }
  ;
rule(<Declarator>,nofunc-declarator-notyp):
    pointer[ptr] direct-nofunc-declarator[decl]      { $$ = $decl.append($ptr); }
  |              direct-nofunc-declarator-notyp
  ;

rule(<Declarator>,func-declarator):
    pointer_opt[ptr] direct-func-declarator[decl]    { $$ = $decl.append($ptr); }
  ;
rule(<Declarator>,func-declarator-notyp):
    pointer[ptr] direct-func-declarator[decl]        { $$ = $decl.append($ptr); }
  |              direct-func-declarator-notyp
  ;

rule(<Declarator>,direct-func-declarator):
    any-identifier[id] direct-declarator-elem-func[el] { $$ = declarator(@id,$id).append($el); }
  | "(" func-declarator[decl] ")"                      { $$ = $decl; }  
  | direct-func-declarator[decl] direct-declarator-elem[el] { $$ = $decl.append($el); }
  ;
rule(<Declarator>,direct-func-declarator-notyp):
    identifier[id] direct-declarator-elem-func[el]     { $$ = declarator(@id,$id).append($el); }
  | "(" func-declarator[decl] ")"                      { $$ = $decl; }  
  | direct-func-declarator-notyp[decl] direct-declarator-elem[el] { $$ = $decl.append($el); }
  ;


// (6.7.6)
rule(<Declarator>,d1):
    any-identifier[id]                           { $$ = declarator(@id, $id); }
  | "(" nofunc-declarator[decl] ")"              { $$ = $decl; }
  ;
rule(<Declarator>,d2):
    d1[decl] direct-declarator-elem-nofunc[el]   { $$ = $decl.append($el); }
  | d2[decl] direct-declarator-elem[el]          { $$ = $decl.append($el); }
  ;
rule(<Declarator>,direct-nofunc-declarator):
    d1
  | d2
  ;
rule(<Declarator>,direct-declarator):
    direct-nofunc-declarator
  | direct-func-declarator
  ;

rule(<Declarator>,d1-notyp):
    identifier[id]                               { $$ = declarator(@id, $id); }
  | "(" nofunc-declarator[decl] ")"              { $$ = $decl; }
  ;
rule(<Declarator>,d2-notyp):
    d1-notyp[decl] direct-declarator-elem-nofunc[el] { $$ = $decl.append($el); }
  | d2-notyp[decl] direct-declarator-elem[el]        { $$ = $decl.append($el); }
  ;
rule(<Declarator>,direct-nofunc-declarator-notyp):
    d1-notyp
  | d2-notyp
  ;

rule(<Declarator>,direct-declarator-notyp):
    direct-nofunc-declarator-notyp
  | direct-func-declarator-notyp
  ;

rule(<DeclElem>,direct-declarator-elem):
    direct-declarator-elem-nofunc
  | direct-declarator-elem-func
  ;

rule(<DeclElem>,direct-declarator-elem-nofunc):
    "[" type-qualifier-list_opt assignment-expression_opt "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list_opt],null,null,$[assignment-expression_opt]); }
  | "[" STATIC type-qualifier-list_opt assignment-expression "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list_opt],@STATIC,null,$[assignment-expression]); }
  | "[" type-qualifier-list STATIC assignment-expression "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list],@STATIC,null,$[assignment-expression]); }
  | "[" type-qualifier-list_opt ASTERISK "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list_opt],null,@ASTERISK,null); }
  ;

rule(<DeclElem>,direct-declarator-elem-func):
    newfunc-decl
  | oldfunc-decl
  ;

rule(<DeclElem>,oldfunc-decl):
    "(" identifier-list_opt ")" { $$ = oldFuncDecl(@$, $[identifier-list_opt]); }
  ;
rule(<DeclElem>,newfunc-decl):
    "(" parameter-type-list ")" { $$ = funcDecl(@$, $[parameter-type-list]); }
  ;

// (6.7.6)
rule(<DeclElem>,pointer,opt):
                  "*"[p] type-qualifier-list_opt  { $$ = pointerDecl(@p,$[type-qualifier-list_opt], null); }
  | pointer[left] "*"[p] type-qualifier-list_opt  { $$ = pointerDecl(@p,$[type-qualifier-list_opt], $left); }
  ;

// (6.7.6)
rule(<SpecNode>,type-qualifier-list,opt):
    type-qualifier
  | type-qualifier-list[left] type-qualifier  { $$ = append($left, $[type-qualifier]); }
  ;

// (6.7.6)
rule(<DeclList>,parameter-type-list):
    parameter-list
  | parameter-list "," "..."            { $$ = $[parameter-list].setEllipsis(); }
  ;

// (6.7.6)
rule(<DeclList>,parameter-list):
    parameter-declaration                           { $$ = declList(null,$[parameter-declaration]); }
  | parameter-list[left] "," parameter-declaration  { $$ = declList($left,$[parameter-declaration]); }
  ;

// (6.7.6)
rule(<DeclInfo>,parameter-declaration):
    declaration-specifiers-nots pointer direct-declarator
        { $$ = declInfo($[direct-declarator].append($pointer), $[declaration-specifiers-nots]); }
  | declaration-specifiers-ts   pointer direct-declarator
        { $$ = declInfo($[direct-declarator].append($pointer), $[declaration-specifiers-ts]); }
  | declaration-specifiers-nots         direct-declarator-notyp
        { $$ = declInfo($[direct-declarator-notyp], $[declaration-specifiers-nots]); }
  | declaration-specifiers-ts           direct-declarator
        { $$ = declInfo($[direct-declarator], $[declaration-specifiers-ts]); }
  | declaration-specifiers-nots pointer direct-abstract-declarator_opt   
        { $$ = declInfo($[direct-abstract-declarator_opt].append($pointer), $[declaration-specifiers-nots]); }
  | declaration-specifiers-ts   pointer direct-abstract-declarator_opt   
        { $$ = declInfo($[direct-abstract-declarator_opt].append($pointer), $[declaration-specifiers-ts]); }
  | declaration-specifiers-nots         direct-abstract-declarator_opt   
        { $$ = declInfo($[direct-abstract-declarator_opt], $[declaration-specifiers-nots]); }
  | declaration-specifiers-ts           direct-abstract-declarator_opt   
        { $$ = declInfo($[direct-abstract-declarator_opt], $[declaration-specifiers-ts]); }
  ;

/*
  In a identifier list (old-style parameter list)
  all but the first identifier cannot redefine a typedef.
  (6.9.1-6)
  (If the first one was a typedef then we would assume that this
  is a new style declaration).
*/
// (6.7.6)
rule(<IdentList>,identifier-list,opt):
    identifier                                { $$ = identListAdd(@identifier, identList(), $identifier); }
  | identifier-list[list] "," any-identifier  { $$ = identListAdd(@[any-identifier], $list, $[any-identifier]); }
  ;

// (6.7.7)
rule(<Qual>,type-name):
    specifier-qualifier-list[slist] abstract-declarator_opt
        { $$ = mkTypeName($[abstract-declarator_opt], declSpec(@slist,$slist)); }
  ;
  
// (6.7.7)
rule(<Declarator>,abstract-declarator):
    pointer                                     { $$ = abstractDeclarator(@pointer).append($pointer); }
  | pointer_opt direct-abstract-declarator      { $$ = $[direct-abstract-declarator].append($pointer_opt); }
  ;

rule(<Declarator>,abstract-declarator_opt):
    abstract-declarator
  | %empty                                      { $$ = abstractDeclarator(yyloc); }
  ;

// (6.7.7)
rule(<Declarator>,direct-abstract-declarator):
    "(" abstract-declarator ")"                                      { $$ = $[abstract-declarator]; }
  | direct-abstract-declarator-elem[elem]                            { $$ = abstractDeclarator(@elem).append($elem); }
  | direct-abstract-declarator direct-abstract-declarator-elem[elem] { $$ = $1.append($elem); }
  ;

rule(<Declarator>,direct-abstract-declarator_opt):
    direct-abstract-declarator
  | %empty                                     { $$ = abstractDeclarator(yyloc); }
  ;

rule(<DeclElem>,direct-abstract-declarator-elem):
    "[" type-qualifier-list assignment-expression_opt "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list],null,null,$[assignment-expression_opt]); }
  | "[" assignment-expression_opt "]"
        { $$ = arrayDecl(@$,null,null,null,$[assignment-expression_opt]); }
  | "[" STATIC type-qualifier-list_opt assignment-expression "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list_opt],@STATIC,null,$[assignment-expression]); }
  | "[" type-qualifier-list STATIC assignment-expression "]"
        { $$ = arrayDecl(@$,$[type-qualifier-list],@STATIC,null,$[assignment-expression]); }
  | "[" ASTERISK "]"
        { $$ = arrayDecl(@$,null,null,@ASTERISK,null); }
  | newfunc-decl
  | "(" ")"
        { $$ = oldFuncDecl(@$,null); }
  ;

// (6.7.9)
initializer:
    assignment-expression               { $$ = ast("initializer",$1); }
  | "{" initializer-list "}"            { $$ = ast("compound-initializer",$2); }
  | "{" initializer-list "," "}"        { $$ = ast("compound-initializer",$2); }
  ;

// (6.7.9)
initializer-list:
    designation_opt initializer         { $$ = ast("initializer-list", ast("initializer-elem",$designation_opt,$initializer)); }
  | initializer-list "," designation_opt initializer { $$ = astAppend($1, ast("initializer-elem",$designation_opt,$initializer)); }
  ;

// (6.7.9)
designation:
    designator-list "="                 { $$ = ast("designation",$1); }
  ;

designation_opt:
    %empty { $$ = null; }
  | designation
  ;
  
// (6.7.9)
designator-list:
    designator                          { $$ = ast("designator-list",$1); }
  | designator-list designator          { $$ = astAppend($1,$2); }
  ;

// (6.7.9)
designator:
    "[" constant-expression "]"         { $$ = ast("designator-index",$[constant-expression]); }
  | "." any-identifier                  { FIXME(); }
// GNU C extension
  | "[" constant-expression[ce1] "..." constant-expression[ce2] "]" { $$ = ast("designator-range",$ce1,$ce2); }
  ;

// (6.7.10)
static_assert-declaration:
    _STATIC_ASSERT "(" constant-expression "," string-literal ")" ";"
        { $$ = ast( $_STATIC_ASSERT, $[constant-expression], $[string-literal] ); }
  ;


// A.2.3 Statements


statement:
    labeled-statement
  | compound-statement
  | expression-statement
  | selection-statement
  | iteration-statement
  | jump-statement
  ;

// (6.8.1)
labeled-statement:
    any-identifier ":" statement                { $$ = ast("label", $statement); }
  | CASE constant-expression ":" statement      { $$ = ast("case", $[constant-expression], $statement); }
  | DEFAULT ":" statement                       { $$ = ast("default", null, $statement); }
// GNU C Extension
  | CASE constant-expression[ce1] "..." constant-expression[ce2] ":" statement { $$ = ast("case-range", $ce1, $ce2, $statement); }
  ;

// (6.8.2)
compound-statement:
    "{" PushBlockScope block-item-list_opt "}"
        { $$ = FIXME(); popScope($PushBlockScope); }
  ;

rule(<Scope>,PushBlockScope):
    %empty { $$ = pushScope(Scope.Kind.BLOCK); }

rule(<Scope>,PushParamScope):
    %empty { $$ = pushScope(Scope.Kind.PARAM); }

rule(<Scope>,PushAggScope):
    %empty { $$ = pushScope(Scope.Kind.AGGREGATE); }

// (6.8.2)
block-item-list:
    block-item                  { FIXME(); }
  | block-item-list block-item  { FIXME(); }
  ;

block-item-list_opt:
    %empty { $$ = null; }
  | block-item-list
  ;

// (6.8.2)
rule(<Ast>,block-item):
    declaration { FIXME(); }
  | statement   { FIXME(); }
  ;

// (6.8.3)
expression-statement:
    expression_opt ";" { $$ = ast("expression-statement",$1); }
  ;

// (6.8.4)
selection-statement:
    IF "(" expression ")" statement                         %prec IF   { $$ = ast("if",$expression,$statement,null); }
  | IF "(" expression ")" statement[s1] ELSE statement[s2]  %prec ELSE { $$ = ast("if",$expression,$s1,$s2); }
  | SWITCH "(" expression ")" statement                                { $$ = ast("switch",$expression,$statement); }
  ;

// (6.8.5)
iteration-statement:
    WHILE "(" expression ")" statement           { $$ = ast("while",$expression,$statement); }
  | DO statement WHILE "(" expression ")" ";"    { $$ = ast("do",$statement,$expression); }
  | FOR "(" expression_opt[e1] ";" expression_opt[e2] ";" expression_opt[e3] ")" statement
      { FIXME(); }
  | FOR "(" PushBlockScope declaration[dcl] expression_opt[e2] ";" expression_opt[e3] ")" statement
      { FIXME(); popScope($PushBlockScope); }
  ;

// (6.8.6)
jump-statement:
    GOTO any-identifier ";"   { FIXME(); }
  | CONTINUE ";"              { $$ = ast("continue"); }
  | BREAK ";"                 { $$ = ast("break"); }
  | RETURN expression_opt ";" { $$ = ast("return", $expression_opt); }
  ;

// A.2.1 Expressions

// (6.5.1)
primary-expression:
    identifier          { $$ = ident($1,@1); }
  | constant
  | string-literal
  | "(" expression ")"  { $$ = $expression; }
  | generic-selection
  ;

// (6.5.1.1)
generic-selection:
    _GENERIC "(" assignment-expression "," generic-assoc-list ")" { FIXME(); }
  ;

// (6.5.1.1)
generic-assoc-list:
    generic-association                         { FIXME(); }
  | generic-assoc-list "," generic-association  { FIXME(); }
  ;

// (6.5.1.1)
generic-association:
    type-name ":" assignment-expression         { FIXME(); }
  | DEFAULT ":" assignment-expression           { FIXME(); }
  ;

// (6.5.2)
postfix-expression:
    primary-expression
  | postfix-expression "[" expression "]"                    { $$ = ast("subscript",$1,$expression); }
  | postfix-expression "(" argument-expression-list_opt ")"  { $$ = ast("call",$1,$[argument-expression-list_opt]); }
  | postfix-expression "." any-identifier                    { FIXME(); }
  | postfix-expression "->" any-identifier                   { FIXME(); }
  | postfix-expression "++"                                  { $$ = ast("post-inc",$1); }
  | postfix-expression "--"                                  { $$ = ast("post-dec",$1); }
  | "(" type-name ")" "{" initializer-list "}"               { FIXME(); }
  | "(" type-name ")" "{" initializer-list "," "}"           { FIXME(); }
  ;

// (6.5.2)
argument-expression-list:
    assignment-expression                               { $$ = ast("argument-expression-list",$1); }
  | argument-expression-list "," assignment-expression  { $$ = astAppend($1,$3); }
  ;

argument-expression-list_opt:
    %empty { $$ = null; }
  | argument-expression-list
  ;

// (6.5.3)
unary-expression:
    postfix-expression
  | "++" unary-expression               { $$ = ast("pre-inc", $2); }
  | "--" unary-expression               { $$ = ast("pre-dec", $2); }
  | unary-operator cast-expression      { $$ = ast($[unary-operator], $[cast-expression]); }
  | SIZEOF unary-expression             { $$ = ast("sizeof-expr",$2); }
  | SIZEOF "(" type-name ")"            { FIXME(); }
  | _ALIGNOF "(" type-name ")"          { FIXME(); }
// GNU C extension
  | "&&" any-identifier                 { FIXME(); }
  ;

// (6.5.3)
unary-operator:
    "&" { $$ = "address-of"; }
  | "*" { $$ = "deref"; }
  | "+" { $$ = "u-plus"; }
  | "-" { $$ = "u-minus"; }
  | "~" { $$ = "binary-not"; }
  | "!" { $$ = "logical-not"; }
  ;

// (6.5.4)
cast-expression:
    unary-expression
  | "(" type-name ")" cast-expression   { FIXME(); }
  ;

// (6.5.5)
multiplicative-expression:
    cast-expression
  | multiplicative-expression "*" cast-expression  { $$ = ast("mul",$1,$3); }
  | multiplicative-expression "/" cast-expression  { $$ = ast("div",$1,$3); }
  | multiplicative-expression "%" cast-expression  { $$ = ast("rem",$1,$3); }
  ;

// (6.5.6)
additive-expression:
    multiplicative-expression
  | additive-expression "+" multiplicative-expression { $$ = ast("add",$1,$3); }
  | additive-expression "-" multiplicative-expression { $$ = ast("sub",$1,$3); }
  ;

// (6.5.7)
shift-expression:
    additive-expression
  | shift-expression "<<" additive-expression        { $$ = ast("shl",$1,$3); }
  | shift-expression ">>" additive-expression        { $$ = ast("shr",$1,$3); }
  ;

// (6.5.8)
relational-expression:
    shift-expression
  | relational-expression "<" shift-expression       { $$ = ast("lt",$1,$3); }
  | relational-expression ">" shift-expression       { $$ = ast("gt",$1,$3); }
  | relational-expression "<=" shift-expression      { $$ = ast("le",$1,$3); }
  | relational-expression ">=" shift-expression      { $$ = ast("ge",$1,$3); }
  ;

// (6.5.9)
equality-expression:
    relational-expression
  | equality-expression "==" relational-expression   { $$ = ast("eq",$1,$3); }
  | equality-expression "!=" relational-expression   { $$ = ast("ne",$1,$3); }
  ;

// (6.5.10)
AND-expression:
    equality-expression
  | AND-expression "&" equality-expression           { $$ = ast("binary-and",$1,$3); }
  ;

// (6.5.11)
exclusive-OR-expression:
    AND-expression
  | exclusive-OR-expression "^" AND-expression       { $$ = ast("binary-xor",$1,$3); }
  ;

// (6.5.12)
inclusive-OR-expression:
    exclusive-OR-expression
  | inclusive-OR-expression "|" exclusive-OR-expression { $$ = ast("binary-or",$1,$3); }
  ;

// (6.5.13)
logical-AND-expression:
    inclusive-OR-expression
  | logical-AND-expression "&&" inclusive-OR-expression  { $$ = ast("logical-and",$1,$3); }
  ;

// (6.5.14)
logical-OR-expression:
    logical-AND-expression
  | logical-OR-expression "||" logical-AND-expression    { $$ = ast("logical-or",$1,$3); }
  ;

// (6.5.15)
conditional-expression:
    logical-OR-expression
  | logical-OR-expression[e1] "?" expression[e2] ":" conditional-expression[e3] { $$ = ast("conditional",$e1,$e2,$e3); }
  ;

// (6.5.16)
assignment-expression:
    conditional-expression
  | unary-expression assignment-operator assignment-expression  { $$ = ast($[assignment-operator],$1,$3); }
  ;

assignment-expression_opt:
    %empty { $$ = null; }
  | assignment-expression
  ;

// (6.5.16)
assignment-operator:
    "="   { $$ = "assign"; }
  | "*="  { $$ = "assign-mul"; }
  | "/="  { $$ = "assign-div"; }
  | "%="  { $$ = "assign-rem"; }
  | "+="  { $$ = "assign-add"; }
  | "-="  { $$ = "assign-sub"; }
  | "<<=" { $$ = "assign-shl"; }
  | ">>=" { $$ = "assign-shr"; }
  | "&="  { $$ = "assign-binary-and"; }
  | "^="  { $$ = "assign-binary-xor"; }
  | "|="  { $$ = "assign-binary-or"; }
  ;

// (6.5.17)
expression:
    assignment-expression
  | expression "," assignment-expression        { $$ = ast("comma",$1,$3); }
  ;

expression_opt:
    %empty { $$ = null; }
  | expression
  ;

// (6.6)
constant-expression:
    conditional-expression
  ;

end_grammar