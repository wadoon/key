package recoder.convenience;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.abstraction.Method;
import recoder.abstraction.ProgramModelElement;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.reference.ReferencePrefix;
import recoder.kit.UnitKit;
import recoder.util.Debug;

import java.util.List;

public class Format {
    public static String toString(String formatText, ModelElement e) {
        Debug.assertNonnull(formatText);
        StringBuffer res = new StringBuffer();
        int len = formatText.length();
        for (int i = 0; i < len; i++) {
            char c = formatText.charAt(i);
            if (c != '%' || i == len - 1) {
                res.append(c);
            } else {
                String name;
                int columns = 1;
                i++;
                c = formatText.charAt(i);
                if (c >= '0' && c <= '9' && i < len - 1) {
                    columns = Math.max(1, c - 48);
                    i++;
                    c = formatText.charAt(i);
                }
                switch (c) {
                    case 'n':
                        if (e instanceof NamedModelElement) {
                            res.append(((NamedModelElement) e).getName());
                            break;
                        }
                        if (e instanceof Identifier) {
                            res.append(((Identifier) e).getText());
                            break;
                        }
                        if (e instanceof CompilationUnit)
                            res.append(((CompilationUnit) e).getPrimaryTypeDeclaration().getName());
                        break;
                    case 'N':
                        if (e instanceof NamedModelElement) {
                            if (e instanceof ProgramModelElement) {
                                res.append(((ProgramModelElement) e).getFullName());
                                if (e instanceof Method)
                                    res.append(toString("%N", ((Method) e).getSignature()));
                                break;
                            }
                            if (e instanceof ReferencePrefix) {
                                res.append(Naming.toPathName((ReferencePrefix) e));
                                break;
                            }
                            res.append(((NamedModelElement) e).getName());
                            break;
                        }
                        if (e instanceof Identifier) {
                            res.append(((Identifier) e).getText());
                            break;
                        }
                        if (e instanceof CompilationUnit)
                            res.append(Naming.toCanonicalName((CompilationUnit) e));
                        break;
                    case 'm':
                        if (e instanceof NamedModelElement) {
                            res.append(((NamedModelElement) e).getName());
                            if (e instanceof Method)
                                res.append(toString("%N", ((Method) e).getSignature()));
                            break;
                        }
                        if (e instanceof Identifier) {
                            res.append(((Identifier) e).getText());
                            break;
                        }
                        if (e instanceof CompilationUnit)
                            res.append(((CompilationUnit) e).getPrimaryTypeDeclaration().getName());
                        break;
                    case 's':
                        if (e instanceof SourceElement)
                            res.append(((SourceElement) e).toSource().trim());
                        break;
                    case 'c':
                        if (e == null) {
                            res.append("null");
                            break;
                        }
                        name = e.getClass().getName();
                        res.append(name.substring(name.lastIndexOf('.') + 1));
                        break;
                    case 'C':
                        if (e == null) {
                            res.append("null");
                            break;
                        }
                        res.append(e.getClass().getName());
                        break;
                    case 'i':
                        if (e != null) {
                            int id = System.identityHashCode(e);
                            if (id < 0) {
                                res.append(Long.toString((id & Integer.MAX_VALUE) | 0x80000000L, 16));
                                break;
                            }
                            res.append(Integer.toString(id, 16));
                        }
                        break;
                    case 'p':
                        if (e instanceof SourceElement) {
                            SourceElement se = (SourceElement) e;
                            se = se.getFirstElement();
                            if (se != null)
                                append(se.getStartPosition(), columns, res);
                        }
                        break;
                    case 'P':
                        if (e instanceof SourceElement) {
                            SourceElement se = (SourceElement) e;
                            SourceElement se2 = se.getFirstElement();
                            if (se2 != null) {
                                append(se2.getStartPosition(), columns, res);
                                res.append('-');
                                se2 = se.getLastElement();
                                append(se2.getEndPosition(), columns, res);
                            }
                        }
                        break;
                    case 'r':
                        if (e instanceof SourceElement) {
                            SourceElement se = (SourceElement) e;
                            se = se.getFirstElement();
                            if (se != null)
                                append(se.getRelativePosition(), columns, res);
                        }
                        break;
                    case 'u':
                        if (e instanceof ProgramElement) {
                            CompilationUnit cu = UnitKit.getCompilationUnit((ProgramElement) e);
                            if (cu != null)
                                res.append(Naming.toCanonicalName(cu));
                        }
                        break;
                    case 'f':
                        if (e instanceof ProgramElement) {
                            CompilationUnit cu = UnitKit.getCompilationUnit((ProgramElement) e);
                            if (cu != null)
                                res.append(cu.getDataLocation());
                        }
                        break;
                    default:
                        res.append('%').append(c);
                        break;
                }
            }
        }
        return res.toString();
    }

    private static void append(SourceElement.Position pos, int columns, StringBuffer buf) {
        int k = 1;
        for (int i = columns; i > 1; ) {
            i--;
            k *= 10;
        }
        int line = -1;
        int col = -1;
        if (pos != SourceElement.Position.UNDEFINED) {
            line = pos.getLine();
            col = pos.getColumn();
        }
        int j;
        for (j = Math.max(1, line); j < k; j *= 10)
            buf.append(' ');
        if (line == -1) {
            buf.append('?');
        } else {
            buf.append(line);
        }
        buf.append('/');
        for (j = Math.max(1, col); j < k; j *= 10)
            buf.append(' ');
        if (col == -1) {
            buf.append('?');
        } else {
            buf.append(col);
        }
    }

    public static String toString(String formatText, List<? extends ModelElement> l) {
        return toString(formatText, "(", ", ", ")", l);
    }

    public static String toString(String formatText, String header, String separator, String footer, List<? extends ModelElement> l) {
        if (l == null)
            return null;
        StringBuffer sb = new StringBuffer(64);
        sb.append(header);
        int s = l.size();
        if (s > 0) {
            sb.append(toString(formatText, l.get(0)));
            for (int i = 1; i < s; i++) {
                sb.append(separator);
                sb.append(toString(formatText, l.get(i)));
            }
        }
        sb.append(footer);
        return sb.toString();
    }

    public static String toString(ProgramElement se) {
        return toString("\"%s\" @%p [%f]", se);
    }

    public static String toString(List<? extends ModelElement> l) {
        return toString("\"%s\" @%p", l);
    }
}
