package c99.parser;

import c99.MiscUtils;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public class Scope
{
public static enum Kind { FILE, BLOCK, PARAM, AGGREGATE, ENUM }

public final Kind kind;
private final Scope m_parent;
private final LinkedList<Decl> m_decls = new LinkedList<Decl>();
private final LinkedList<Decl> m_tags = new LinkedList<Decl>();

private boolean m_error;
private int m_level;

public Scope ( Kind kind, final Scope parent )
{
  this.kind = kind;
  m_parent = parent;
  m_level = parent != null ? parent.m_level + 1 : 0;
}

public final Scope getParent ()
{
  return m_parent;
}

public final void orError ( boolean err )
{
  m_error |= err;
}

public boolean isError ()
{
  return m_error;
}

public void debugDecl ( String msg, Decl decl )
{
  if (DeclActions.DEBUG_DECL)
  {
    MiscUtils.printIndent( m_level * 4, System.out );
    System.out.println( msg + " "+ decl.toString() );
  }
}
private void debug ( Decl decl )
{
  debugDecl( "push", decl );
}

public final void pushDecl ( Decl decl )
{
  orError( decl.isError() );
  m_decls.add( decl );

  assert decl.listPrev == null;
  if (decl.symbol != null)
  {
    decl.listPrev = decl.symbol.topDecl;
    decl.symbol.topDecl = decl;
  }

  if (DeclActions.DEBUG_DECL)
    debug( decl );
}

public final void pushTag ( Decl decl )
{
  orError( decl.isError() );
  m_tags.add( decl );

  assert decl.listPrev == null;
  if (decl.symbol != null)
  {
    decl.listPrev = decl.symbol.topTag;
    decl.symbol.topTag = decl;
  }

  if (DeclActions.DEBUG_DECL)
    debug( decl );
}

public final void pop ()
{
  // Iterate in reverse order, as we could have the same symbol in the scope more than once
  for (Iterator<Decl> it = m_decls.descendingIterator(); it.hasNext();)
  {
    final Decl d = it.next();
    if (d.symbol != null)
    {
      assert d.symbol.topDecl == d;
      d.symbol.topDecl = d.listPrev;
      d.listPrev = null;
    }
  }
  for (Iterator<Decl> it = m_tags.descendingIterator(); it.hasNext();)
  {
    final Decl d = it.next();
    if (d.symbol != null)
    {
      assert d.symbol.topTag == d;
      d.symbol.topTag = d.listPrev;
      d.listPrev = null;
    }
  }
}

public final List<Decl> decls ()
{
  return m_decls;
}

}
