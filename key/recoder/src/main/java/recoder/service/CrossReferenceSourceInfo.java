package recoder.service;

import recoder.abstraction.Package;
import recoder.abstraction.*;
import recoder.java.reference.*;

import java.util.List;

public interface CrossReferenceSourceInfo extends SourceInfo {
    List<MemberReference> getReferences(Method paramMethod);

    List<ConstructorReference> getReferences(Constructor paramConstructor);

    List<VariableReference> getReferences(Variable paramVariable);

    List<FieldReference> getReferences(Field paramField);

    List<TypeReference> getReferences(Type paramType);

    List<PackageReference> getReferences(Package paramPackage);
}
