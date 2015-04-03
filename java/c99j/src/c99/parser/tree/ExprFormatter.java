package c99.parser.tree;

import c99.MiscUtils;
import c99.SourceRange;

import java.io.PrintWriter;

public class ExprFormatter
{
private static final int INDENT_STEP = 4;

public static void format ( int indent, PrintWriter out, TExpr.Expr e )
{
  MiscUtils.printIndent( indent, out );
  if (e == null)
  {
    out.println( "<null>" );
    return;
  }

  String details = e.formatDetails();
  out.format( "%s:'%s'%s <%s>\n", e.getCode().name(), e.getQual().readableType(),
          details, SourceRange.formatRange(e) );
  for ( int i = 0, c = e.getNumChildren(); i < c; ++i )
    format( indent + INDENT_STEP, out, e.getChild( i ) );
  out.flush();
}

public static void format ( int indent, PrintWriter out, TInit.Value v )
{
  MiscUtils.printIndent( indent, out );
  if (v == null)
  {
    out.println( "<null>" );
    return;
  }

  out.format( "%s%s: %s\n", v.isScalar() ? "TInit.Scalar" : "TInit.Aggregate",
      v.isError() ? "[error]" : "", v.getQual().readableType() );

  indent += INDENT_STEP;
  if (v.isScalar())
    format( indent, out, v.asScalar().getValue() );
  else
  {
    TInit.Aggregate agg = v.asAggregate();
    for ( int i = 0, l = agg.getLength(); i < l; ++i )
      format( indent, out, agg.getElem( i ) );
  }
}

}
