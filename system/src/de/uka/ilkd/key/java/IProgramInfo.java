package de.uka.ilkd.key.java;

import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;

public interface IProgramInfo {

	/**
	 * convenience method that returns the Recoder-to-KeY mapping underlying
	 * the KeYProgModelInfo of this JavaInfo
	 */
	public abstract KeYRecoderMapping rec2key();

	/**
	 * copies this JavaInfo and uses the given Services object as the
	 * Services object of the copied JavaInfo
	 * @param serv the Services the copy will use and vice versa
	 * @return a copy of the JavaInfo
	 */
	public abstract IProgramInfo copy(IServices serv);

	/**
	 * returns the services associated with this JavaInfo
	 */
	public abstract IServices getServices();

	/**
	 * returns the full name of a given {@link
	 * de.uka.ilkd.key.java.abstraction.KeYJavaType}. 
	 * @param t the KeYJavaType including the package prefix
	 * @return the full name
	 */
	public abstract String getFullName(KeYJavaType t);

	/**
	 * looks up the fully qualifying name given by a String 
	 * in the list of all available
	 * KeYJavaTypes in the Java model
	 * @param fullName the String
	 * @return the KeYJavaType with the name of the String
	 */
	public abstract KeYJavaType getTypeByName(String fullName);

	/**
	 * looks up a KeYJavaType with given name. If the name is a fully
	 * qualifying name with package prefix an element with this full name is
	 * taken. If the name does not contain a full package prefix some
	 * KeYJavaType with this short name is taken.     
	 * @param className the name to look for (either full or short)
	 * @return a class matching the name
	 */
	public abstract KeYJavaType getTypeByClassName(String className);

	/**
	 * returns all known KeYJavaTypes of the current
	 * program type model
	 * @return all known KeYJavaTypes of the current
	 * program type model
	 */
	public abstract Set<KeYJavaType> getAllKeYJavaTypes();

	/**
	 * returns a KeYJavaType (either primitive of object type) having the
	 * full name of the given String fullName 
	 * @param fullName a String with the type name to lookup 
	 */
	public abstract KeYJavaType getKeYJavaType(String fullName);

	/**
	 * this is an alias for getTypeByClassName
	 */
	public abstract KeYJavaType getKeYJavaTypeByClassName(String className);

	/**
	 * returns true iff the given subType KeYJavaType is a sub type of the
	 * given KeYJavaType superType.
	 */
	public abstract boolean isSubtype(KeYJavaType subType, KeYJavaType superType);

	public abstract boolean isInterface(KeYJavaType t);

	/** 
	 * returns a KeYJavaType having the given sort
	 */
	public abstract KeYJavaType getKeYJavaType(Sort sort);

	/**
	 * returns the KeYJavaType belonging to the given Type t
	 */
	public abstract KeYJavaType getKeYJavaType(Type t);

	/**
	 * returns all methods from the given Type as IProgramMethods
	 */
	public abstract ImmutableList<IProgramMethod> getAllProgramMethods(
			KeYJavaType kjt);

	/**
	 * returns all methods declared in the given Type as IProgramMethods
	 */
	public abstract ImmutableList<IProgramMethod> getAllProgramMethodsLocallyDeclared(
			KeYJavaType kjt);

	public abstract Sort nullSort();

	/**
	 * returns the default execution context. This is equiavlent to executing the program
	 * in a static method of a class placed in the default package 
	 * @return the default execution context
	 */
	public abstract ExecutionContext getDefaultExecutionContext();

	/**
	 * returns all proper subtypes of a given type
	 * @param type the KeYJavaType whose subtypes are returned
	 * @return list of all subtypes
	 */
	public abstract ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType type);

	/**
	 * returns all supertypes of a given type
	 * @param type the KeYJavaType whose supertypes are returned
	 * @return list of all supertypes
	 */
	public abstract ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType type);

	/**
	 * returns the list of all common subtypes of types <tt>k1</tt> and <tt>k2</tt>
	 * (inclusive one of them if they are equal or subtypes themselves)
	 * attention: <tt>Null</tt> is not a jav atype only a logic sort, i.e.
	 * if <tt>null</tt> is the only element shared between <tt>k1</tt> and <tt>k2</tt> 
	 * the returned list will be empty
	 * 
	 * @param k1 the first KeYJavaType denoting a class type
	 * @param k2 the second KeYJavaType denoting a classtype
	 * @return the list of common subtypes of types <tt>k1</tt> and <tt>k2</tt>
	 */
	public abstract ImmutableList<KeYJavaType> getCommonSubtypes(
			KeYJavaType k1, KeYJavaType k2);

	/**
	 * Returns the special symbol <code>&lt;inv&gt;</code> which stands for the class invariant of an object.
	 */
	public abstract IObserverFunction getInv();

}