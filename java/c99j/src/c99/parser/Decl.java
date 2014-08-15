package c99.parser;

import c99.ISourceRange;
import c99.SourceRange;
import c99.Types.*;

public class Decl extends SourceRange
{

public static enum Kind
{
  VAR,
  ENUM_CONST,
  TAG,
}
Decl prev;

public final Decl importedDecl;
public final Kind kind;
public final Scope scope;
public       SClass sclass;
public final Linkage linkage;
public final Symbol symbol;
public final Qual type;
public boolean defined;
public boolean error;


public Decl (
  ISourceRange rng, Kind kind, Scope scope, SClass sclass, Linkage linkage, Symbol symbol, Qual type,
  boolean defined, boolean error
)
{
  super(rng);
  this.importedDecl = null;
  this.kind = kind;
  this.scope = scope;
  this.sclass = sclass;
  this.linkage = linkage;
  this.symbol = symbol;
  this.type = type;
  this.error = error;
}

/** Import a declaration into the current scope */
public Decl ( ISourceRange rng, Scope scope, Decl importedDecl, boolean error )
{
  super(rng);
  assert importedDecl.scope != scope;
  assert importedDecl.importedDecl == null;

  this.importedDecl = importedDecl;
  this.kind = importedDecl.kind;
  this.scope = scope;
  this.sclass = importedDecl.sclass;
  this.linkage = importedDecl.linkage;
  this.symbol = importedDecl.symbol;
  this.type = importedDecl.type;
  this.error = importedDecl.error | error;
}

}
