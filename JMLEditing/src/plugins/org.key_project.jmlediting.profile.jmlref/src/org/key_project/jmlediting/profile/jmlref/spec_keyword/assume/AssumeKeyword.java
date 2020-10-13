package org.key_project.jmlediting.profile.jmlref.spec_keyword.assume;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.SemicolonClosedKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.requires.RequiresValueKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The assume keyword.
 *
 * @author Lukas Grätz
 *
 */
public class AssumeKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new instance for the assume keyword.
    */
   public AssumeKeyword() {
      super("assume", "assume_redundantly");
   }

   @Override
   public String getDescription() {
      return "The assume statement is used to tell that the given predicate is assumed to be true, and thus need not be checked.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * assume-statement ::= assume-keyword predicate; <br>
             * assume-keyword ::= assume | assume_redundantly
             */
            return alt(
                  new PredicateParser(profile),
                  keywords(JMLProfileHelper.filterKeywords(profile,
                        RequiresValueKeywordSort.INSTANCE), profile));
         }
      };
   }

}
