package c99.parser.pp;

public interface IPreprOptions
{
boolean getSignedChar ();
boolean getNoStdInc ();
boolean getGccExtensions ();
boolean getWarnUndef ();

int getMaxIncludeDepth ();
}
