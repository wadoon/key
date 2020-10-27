package recoder.bytecode;

public interface AccessFlags {
    int PUBLIC = 1;

    int PRIVATE = 2;

    int PROTECTED = 4;

    int STATIC = 8;

    int FINAL = 16;

    int SUPER = 32;

    int SYNCHRONIZED = 32;

    int VOLATILE = 64;

    int BRIDGE = 64;

    int TRANSIENT = 128;

    int VARARGS = 128;

    int NATIVE = 256;

    int INTERFACE = 512;

    int ABSTRACT = 1024;

    int STRICT = 2048;

    int SYNTHETIC = 4096;

    int ANNOTATION = 8192;

    int ENUM = 16384;
}
