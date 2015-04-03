package c99.parser.tree;

import c99.ISourceRange;
import c99.SourceRange;
import c99.Types;

import java.util.ArrayList;

public final class TInit
{
private TInit () {}

public static abstract class Value implements ISourceRange
{
  protected final Types.Qual m_qual;

  public Value ( Types.Qual qual )
  {
    this.m_qual = qual;
  }

  public final Types.Qual getQual ()
  {
    return m_qual;
  }

  public abstract boolean isError ();

  public final boolean isScalar () { return this instanceof Scalar; }
  public final Scalar asScalar () { return (Scalar)this; }

  public final boolean isAggregate () { return this instanceof Aggregate; }
  public final Aggregate asAggregate () { return (Aggregate)this; }
}

public static final class Scalar extends Value
{
  private TExpr.Expr m_value;

  public Scalar ( Types.Qual qual )
  {
    super( qual );
  }

  @Override
  public boolean isError ()
  {
    return m_value != null && m_value.isError();
  }

  public TExpr.Expr getValue () { return m_value; }
  public void setValue ( TExpr.Expr value ) { m_value = value; }

  public String getFileName () { return m_value.getFileName(); }
  public int getLine1 () { return m_value.getLine1(); }
  public int getCol1 () { return m_value.getCol1(); }
  public String getFileName2 () { return m_value.getFileName2(); }
  public int getLine2 () { return m_value.getLine2(); }
  public int getCol2 () { return m_value.getCol2(); }
}

public static final class Aggregate extends Value
{
  private final ArrayList<Value> m_elems;
  private final SourceRange m_sourceRange;
  private boolean m_error;

  public Aggregate ( Types.Qual qual, int capacity )
  {
    super( qual );
    m_elems = new ArrayList<Value>( capacity );
    m_sourceRange = new SourceRange();
  }
  public Aggregate ( Types.Qual qual )
  {
    this( qual, 8 );
  }

  public void setError ()
  {
    m_error = true;
  }

  @Override
  public boolean isError ()
  {
    return m_error;
  }

  public int getLength ()
  {
    return m_elems.size();
  }

  /**
   * Get an element. Elements outside of the array range are returned as {@code null}
   * @param index
   * @return
   */
  public Value getElem ( int index )
  {
    return index < m_elems.size() ? m_elems.get( index ) : null;
  }

  /**
   * Set an element, resizing the array if necessary
   * @param index
   * @param value
   */
  public void setElem ( int index, Value value )
  {
    m_error |= value.isError();

//    m_sourceRange.union( value ); // FIXME
    if (index == m_elems.size())
      m_elems.add( value );
    else if (index < m_elems.size())
    {
      m_elems.set( index, value );
    }
    else
    {
      m_elems.ensureCapacity( index + 1 );
      for ( int i = m_elems.size(); i < index; ++i )
        m_elems.add(null);
      m_elems.add( value );
    }
  }

  public String getFileName () { return m_sourceRange.getFileName(); }
  public int getLine1 () { return m_sourceRange.getLine1(); }
  public int getCol1 () { return m_sourceRange.getCol1(); }
  public String getFileName2 () { return m_sourceRange.getFileName2(); }
  public int getLine2 () { return m_sourceRange.getLine2(); }
  public int getCol2 () { return m_sourceRange.getCol2(); }
}

}
