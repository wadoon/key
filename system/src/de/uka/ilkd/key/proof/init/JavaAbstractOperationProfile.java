package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.UseAbstractOperationContractRule;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;

/*
 * This profile is used when verifying in the abstract mode.
 * The difference lies in the initialization of builtInRules with
 * UseAbstractOperationContractRule instead of UseOperationContractRules
 * 
 */
public class JavaAbstractOperationProfile extends JavaProfile {

	private static final String NAME = "Java Abstract Operation Profile";

	/**
	 * <p>
	 * The default instance of this class.
	 * </p>
	 * <p> 
	 * It is typically used in the {@link Thread} of the user interface.
	 * Other instances of this class are typically only required to 
	 * use them in different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 */
	public static JavaAbstractOperationProfile defaultInstance; 



	public JavaAbstractOperationProfile() {
		super();
	}   

	
	@Override
	public ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();
        
  
        //contract insertion rule,ATTENTION: ProofMgt relies on the fact 
        // that Contract insertion rule is the FIRST element of this list!
        //builtInRules = builtInRules.prepend(UseAbstractOperationContractRule.INSTANCE);
        builtInRules = builtInRules.prepend(UseAbstractOperationContractRule.INSTANCE);
        return builtInRules;
	}

	/**
	 * the name of the profile
	 */
	public String name() {
		return NAME;
	}


	/**
	 * <p>
	 * Returns the default instance of this class.
	 * </p>
	 * <p>
	 * It is typically used in the {@link Thread} of the user interface.
	 * Other instances of this class are typically only required to 
	 * use them in different {@link Thread}s (not the UI {@link Thread}).
	 * </p>
	 * @return The default instance for usage in the {@link Thread} of the user interface.
	 */
	public static synchronized JavaProfile getDefaultInstance() {
		if (defaultInstance == null) {
			defaultInstance = new JavaAbstractOperationProfile();
		}
		return defaultInstance;
	}


}
