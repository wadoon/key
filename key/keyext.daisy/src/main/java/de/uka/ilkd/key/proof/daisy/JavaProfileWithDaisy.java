package de.uka.ilkd.key.proof.daisy;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.BuiltInRule;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


public class JavaProfileWithDaisy extends JavaProfile {

    private static final JavaProfileWithDaisy INSTANCE = new JavaProfileWithDaisy();

    public static class Resolver implements DefaultProfileResolver {

        @Override
        public String getProfileName() {
            return "Java Profile for Daisy";
        }

        @Override
        public Profile getDefaultProfile() {
            return INSTANCE;
        }
    }

    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> result =
                ImmutableSLList.<BuiltInRule>nil().
                        prepend(DaisyBoundsBuiltinRule.INSTANCE);
        result.prepend(super.initBuiltInRules());
        return result;
    }
}
