package org.key_project.editor;

import bibliothek.gui.dock.common.CLocation;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.MultipleCDockableFactory;
import bibliothek.gui.dock.common.MultipleCDockableLayout;
import bibliothek.util.xml.XElement;
import de.uka.ilkd.key.gui.MainWindow;
import lombok.Data;
import org.fife.ui.rsyntaxtextarea.CodeTemplateManager;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.Theme;
import org.fife.ui.rsyntaxtextarea.templates.CodeTemplate;
import org.fife.ui.rsyntaxtextarea.templates.StaticCodeTemplate;
import org.jetbrains.annotations.NotNull;
import org.key_project.editor.java.JavaJMLEditorFactory;
import org.key_project.editor.keyfile.KeyEditorFactory;
import org.key_project.util.RandomName;

import javax.swing.filechooser.FileFilter;
import java.io.*;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class EditorFacade {
    private static Theme EDITOR_THEME;
    private static List<EditorFactory> factories = new ArrayList<>();
    private static EditorDockableFactory editorDockableFactory = new EditorDockableFactory();

    static {
        register(new FallbackEditorFactory());
        register(new JavaJMLEditorFactory());
        register(new KeyEditorFactory());
    }

    static MultipleCDockableFactory<?, ?> getEditorDockableFactory() {
        return editorDockableFactory;
    }

    public static void register(EditorFactory factory) {
        factories.add(0, factory);
    }

    public static Editor open(String mimeType) {
        Editor e;
        for (EditorFactory it : factories) {
            if ((e = it.open(mimeType)) != null)
                return e;
        }
        return null;
    }

    public static Editor open(Path path) {
        Editor e;
        try {
            for (EditorFactory it : factories) {
                if ((e = it.open(path)) != null)
                    return e;
            }
        } catch (IOException e1) {
            e1.printStackTrace();
        }
        return null;
    }

    public static void addEditor(Editor editor, MainWindow mainWindow) {
        DefaultMultipleCDockable dockable = editor.getDockable();
        mainWindow.getDockControl().addDockable(dockable);
        dockable.setLocation(CLocation.base().normalWest(.2));
        dockable.setVisible(true);
    }

    public static List<EditorFactory> getEditorFactories() {
        return factories;
    }

    public static Theme getEditorTheme() {
        if (EDITOR_THEME == null) {
            InputStream themeRes = EditorFacade
                    .class.getResourceAsStream("org/fife/ui/rsyntaxtextarea/themes/eclipse.xml");
            if (null != themeRes) {
                try {
                    EDITOR_THEME = Theme.load(themeRes);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }
        return EDITOR_THEME;
    }

    public static Stream<FileFilter> getFileFilters() {
        return getEditorFactories().stream().map(it ->
                new FileFilter() {
                    @Override
                    public boolean accept(File f) {
                        return it.getFileSuffixes().stream().anyMatch(it -> f.getName().endsWith(it));
                    }

                    @Override
                    public String getDescription() {
                        return it.getName() + " ("+ String.join(", ", it.getFileSuffixes()) +")";
                    }
                }
        );
    }

    @Data
    public static class EditorDockableData implements MultipleCDockableLayout {
        public static final String NEW_LINE_REPLACEMENT = "%%N";
        private String path, textContent, mimeType;

        @Override
        public void writeStream(DataOutputStream dataOutputStream) throws IOException {
            dataOutputStream.writeUTF(path);
            dataOutputStream.writeUTF(textContent);
            dataOutputStream.writeUTF(mimeType);
        }

        @Override
        public void readStream(DataInputStream dataInputStream) throws IOException {
            path = dataInputStream.readUTF();
            textContent = dataInputStream.readUTF();
            mimeType = dataInputStream.readUTF();
        }

        @Override
        public void writeXML(XElement xElement) {
            xElement.addString("PATH", path);
            xElement.addString("TEXT_CONTENT",
                    textContent.replace("\n", NEW_LINE_REPLACEMENT));
            xElement.addString("MIMETYPE", mimeType);
        }

        @Override
        public void readXML(XElement xElement) {
            path = xElement.getString("PATH");
            mimeType = xElement.getString("MIMETYPE");
            textContent = xElement.getString("TEXT_CONTENT")
                    .replace(NEW_LINE_REPLACEMENT, "\n");
        }
    }

    public static class EditorDockableFactory
            implements MultipleCDockableFactory<Editor, EditorDockableData> {
        @Override
        public EditorDockableData write(Editor defaultMultipleCDockable) {
            Editor editor = defaultMultipleCDockable;
            EditorDockableData dockableData = create();
            dockableData.path = (editor.getPath() == null ? "" : editor.getPath().toString());
            dockableData.textContent = editor.getText();
            dockableData.mimeType = editor.getMimeType();
            return dockableData;
        }

        @Override
        public Editor read(EditorDockableData editorDockableData) {
            if (editorDockableData.path != null && !editorDockableData.path.isBlank())
                return open(Paths.get(editorDockableData.path));
            else {
                Editor e = open(editorDockableData.mimeType);
                assert e != null;
                e.setText(editorDockableData.textContent);
                return e;
            }
        }

        @Override
        public boolean match(Editor defaultMultipleCDockable,
                             EditorDockableData editorDockableData) {
            return editorDockableData.equals(write(defaultMultipleCDockable));
            /*return Objects.equals(editor.getPath().toString(), editorDockableData.path)
                    && Objects.equals(editor.getMimeType(), editorDockableData.mimeType)
                    && Objects.equals(editor.getText(), editorDockableData.textContent);
                   */
        }

        @Override
        public EditorDockableData create() {
            return new EditorDockableData();
        }
    }

    static class FallbackEditorFactory implements EditorFactory {
        @Override
        public String getName() {
            return "text/plain";
        }

        @Override
        public @NotNull Collection<String> getFileSuffixes() {
            return Collections.singleton("txt");
        }

        @Override
        public Editor open(Path path) throws IOException {
            Editor e = open();
            e.setText(Files.readString(path));
            e.setDirty(false);
            e.setPath(path);
            return e;
        }

        @Override
        public Editor open(String mimeType) {
            return open();
        }

        @Override
        public Editor open() {
            Editor e = new Editor(RandomName.getRandomName("-") + ".txt");
            e.setMimeType("text/plain");
            return e;
        }
    }

    public static void loadSnippets(URL snippetUrl) {
        if (snippetUrl != null) {
            try (InputStream s = new BufferedInputStream(snippetUrl.openStream())) {
                CodeTemplateManager ctm = RSyntaxTextArea.getCodeTemplateManager();
                Properties p = new Properties();
                p.loadFromXML(s);
                p.forEach((key, value) -> {
                    String v = value.toString();
                    String[] t = v.split("[#]");
                    if (t.length > 1) {
                        CodeTemplate ct = new StaticCodeTemplate(key.toString(), t[0], t[1]);
                        ctm.addTemplate(ct);
                    } else {
                        CodeTemplate ct = new StaticCodeTemplate(key.toString(), v, null);
                        ctm.addTemplate(ct);
                    }
                });
                System.out.println("Java snippets loaded");
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else {
            System.err.println("Could not find snippets.xml");
        }
    }
}
