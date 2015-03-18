package c99.parser;

import c99.Constant;
import c99.parser.tree.TExpr;

public class InitActions extends DeclActions
{

private final int validateIndex ( TExpr.ArithConstant index )
{
  Constant.IntC vindex = (Constant.IntC) index.getValue();
  long nindex;

  if (!vindex.fitsInLong() || (nindex = vindex.asLong()) > Integer.MAX_VALUE)
  {
    error( index, "index integer overflow" );
    return -1;
  }

  if (nindex < 0 )
  {
    error( index, "negative designator index" );
    return -1;
  }

  return (int)nindex;
}

public final InitAst.Designator indexDesignator ( CParser.Location loc, TExpr.ArithConstant index )
{
  int nindex = validateIndex( index );
  return new InitAst.IndexDesignator( loc, nindex < 0, nindex >= 0 ? nindex : 0 );
}

public final InitAst.Designator fieldDesignator ( CParser.Location loc, Symbol ident )
{
  return new InitAst.FieldDesignator( loc, false, ident );
}

public final InitAst.Designator rangeDesignator ( CParser.Location loc, TExpr.ArithConstant first, TExpr.ArithConstant last )
{
  pedWarning( loc, "range designators are a GCC-extension" );

  int nfirst = validateIndex( first );
  int nlast = validateIndex( last );

  if (nlast < 0)
    nfirst = -1;

  if (nfirst >= 0 && nlast < nfirst)
  {
    error( loc, "array designator range [%d ... %d] is empty", nfirst, nlast );
    nfirst = -1;
  }

  return new InitAst.RangeDesignator( loc, nfirst < 0, nfirst >= 0 ? nfirst : 0, nfirst >= 0 ? nlast : 0 );
}

public final InitAst.Initializer initializer ( CParser.Location loc, TExpr.Expr expr )
{
  return new InitAst.InitializerExpr( loc, expr );
}

public final InitAst.InitializerList initializerList (
  CParser.Location loc, InitAst.InitializerList list, InitAst.Designator designation, InitAst.Initializer elem
)
{
  if (list == null)
    list = new InitAst.InitializerList( loc );
  elem.setDesignation( designation );
  list.add( elem );
  list.setRange( loc );
  return list;
}

}
