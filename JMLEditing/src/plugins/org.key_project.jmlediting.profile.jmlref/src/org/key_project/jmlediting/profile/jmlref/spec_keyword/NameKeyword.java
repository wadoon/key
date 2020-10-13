package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.util.Lexicals;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;

/**
 * The name keyword.
 *
 * @author Lukas Grätz
 *
 */
public class NameKeyword extends AbstractGenericSpecificationKeyword {

    public NameKeyword() {
        super("name");
    }

    @Override
    public String getDescription() {
        return "The name statement gives the specification a name (not part of the JML standard).";
    }

    @Override
    public IKeywordParser createParser() {
       return new SemicolonClosedKeywordParser() {

          @Override
          protected ParseFunction createContentParseFunction(
                final IJMLExpressionProfile profile) {
             /**
              * spec=SPEC_NAME name=STRING_LITERAL SEMICOLON
              */
             return Lexicals.stringLiteral();
          }
       };
    }
}
