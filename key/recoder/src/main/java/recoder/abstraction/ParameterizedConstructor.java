/**
 * 
 */
package recoder.abstraction;

import recoder.service.ImplicitElementInfo;

/**
 * @author Tobias Gutzmann
 *
 */
public class ParameterizedConstructor extends ParameterizedMethod implements
		Constructor {

	/**
	 * @param genericMethod
	 * @param parentClassType
	 * @param service
	 */
	public ParameterizedConstructor(Method genericMethod,
			ParameterizedType parentClassType, ImplicitElementInfo service) {
		super(genericMethod, parentClassType, service);
		// TODO Auto-generated constructor stub
	}

}
