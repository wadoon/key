package recoder.io;

import recoder.Service;
import recoder.bytecode.ClassFile;

import java.util.List;

public interface ClassFileRepository extends Service {
    DataLocation findClassFile(String paramString);

    ClassFile getClassFile(String paramString);

    List<ClassFile> getKnownClassFiles();
}
