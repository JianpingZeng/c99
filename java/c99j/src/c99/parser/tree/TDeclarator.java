package c99.parser.tree;

import c99.ISourceRange;
import c99.SourceRange;
import c99.parser.*;

import java.util.ArrayList;

/**
 * Created by tmikov on 1/5/15.
 */
public final class TDeclarator extends SourceRange
{
public final Symbol ident;
Elem top;
Elem bottom;

public TDeclarator ( ISourceRange rng, final Symbol ident )
{
  super( rng );
  this.ident = ident;
}

public TDeclarator append ( Elem next )
{
  if (next != null)
  {
    if (bottom != null)
      bottom.append( next );
    else
      top = next;
    bottom = next;
  }
  return this;
}

public static interface Visitor
{
  public boolean pointer ( int depth, PointerElem elem );
  public boolean array ( int depth, ArrayElem elem );
  public boolean function ( int depth, FuncElem elem );
}

public boolean visitPost ( Visitor v )
{
  return this.top == null || visitHelper( 1, this.top, v );
}

// FIXME: prevent unbound recursion. Limit the depth of the type chain
private boolean visitHelper ( int depth, Elem elem, Visitor v )
{
  if (elem.to != null)
    if (!visitHelper( depth+1, elem.to, v ))
      return false;

  switch (elem.code)
  {
  case ASTERISK:  return v.pointer( depth, (PointerElem)elem );
  case L_BRACKET: return v.array( depth, (ArrayElem)elem );
  case L_PAREN:   return v.function( depth, (FuncElem)elem );
  default:
    assert false : "Invalid type code " + elem.code;
  }
  return false;
}

/**
 * Created by tmikov on 1/5/15.
 */
public static abstract class Elem extends SourceRange
{
  public final Code code;
  public Elem to;

  public Elem ( CParser.Location loc, Code code )
  {
    this.code = code;
    BisonLexer.setLocation( this, loc );
  }

  public Elem append ( Elem next )
  {
    if (next != null)
    {
      assert this.to == null;
      this.to = next;
    }
    return this;
  }
}

public static final class PointerElem extends Elem
{
  public final TSpecNode qualList;

  public PointerElem ( CParser.Location loc, TSpecNode qualList )
  {
    super( loc, Code.ASTERISK );
    this.qualList = qualList;
  }
}

// FIXME: size
public static final class ArrayElem extends Elem
{
  public TSpecNode qualList;
  public SourceRange _static;
  public SourceRange asterisk;

  public ArrayElem ( CParser.Location loc, TSpecNode qualList, CParser.Location _static, CParser.Location asterisk )
  {
    super( loc, Code.L_BRACKET );
    this.qualList = qualList;
    this._static = _static == null ? null : BisonLexer.fromLocation( _static );
    this.asterisk = asterisk == null ? null : BisonLexer.fromLocation( asterisk );
  }
}

public static final class FuncElem extends Elem
{
  public final TDeclList declList;
  public final TIdentList identList;

  public FuncElem ( CParser.Location loc, TDeclList declList, TIdentList identList )
  {
    super( loc, Code.L_PAREN );
    this.declList = declList;
    this.identList = identList;
  }
}

}
