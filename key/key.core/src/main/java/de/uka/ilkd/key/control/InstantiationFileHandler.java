package de.uka.ilkd.key.control;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.PathConfig;

import javax.annotation.Nonnull;
import java.io.*;
import java.util.*;

/**
 *
 */
public final class InstantiationFileHandler {
    private static final String INSTANTIATION_DIR =
            PathConfig.getKeyConfigDir() + File.separator + "instantiations";

    public static final String SEPARATOR1 = "<<<<<<";

    public static final String SEPARATOR2 = ">>>>>>";

    public static final String LINE_END = System.getProperty("line.separator");

    public static final int SAVE_COUNT = 10;

    private static HashMap<String, List<List<String>>> hm;

    public static boolean hasInstantiationListsFor(Taclet taclet) {
        return hasInstantiationListsFor(taclet.name().toString());
    }

    public static boolean hasInstantiationListsFor(String taclet) {
        if (hm == null) {
            createHashMap();
        }
        return hm.containsKey(taclet);
    }

    @Nonnull
    public static List<List<String>> getInstantiationListsFor(Taclet taclet) {
        return getInstantiationListsFor(taclet.name().toString());
    }

    @Nonnull
    public static List<List<String>> getInstantiationListsFor(String taclet) {
        if (hasInstantiationListsFor(taclet)) {
            if (hm.get(taclet) == null) {
                return createListFor(taclet);
            }
            return hm.get(taclet);
        }
        return Collections.emptyList();
    }

    private static void createHashMap() {
        File dir = new File(INSTANTIATION_DIR);
        if (!dir.exists()) {
            dir.mkdirs();
        }
        String[] instFiles = dir.list();
        if (instFiles == null) {
            hm = new LinkedHashMap<>(0);
        } else {
            // Avoid resizing of HashMap
            hm = new LinkedHashMap<>(instFiles.length + 1, 1);
            for (String instFile : instFiles) {
                hm.put(instFile, null);
            }
        }
    }

    private static List<List<String>> createListFor(Taclet taclet) {
        return createListFor(taclet.name().toString());
    }

    private static List<List<String>> createListFor(String name) {
        List<List<String>> instList = new LinkedList<>();
        List<String> instantiations = new LinkedList<>();

        try (var br = new BufferedReader(new FileReader(getFile(name)))) {
            var sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) {
                if (line.equals(SEPARATOR1)) {
                    if (sb.length() > 0) {
                        instantiations.add(sb.toString());
                    }
                    sb = new StringBuilder();
                    if (!instantiations.isEmpty()) {
                        instList.add(instantiations);
                    }
                    instantiations = new LinkedList<>();
                } else if (line.equals(SEPARATOR2)) {
                    if (sb.length() > 0) {
                        instantiations.add(sb.toString());
                    }
                    sb = new StringBuilder();
                } else {
                    if (sb.length() > 0) {
                        sb.append(LINE_END);
                    }
                    sb.append(line);
                }
            }

            if (sb.length() > 0) {
                instantiations.add(sb.toString());
            }
        } catch (IOException ignored) {
        }
        if (!instantiations.isEmpty()) {
            instList.add(instantiations);
        }
        hm.put(name, instList);
        return instList;
    }

    private static File getFile(String name) {
        return new File(INSTANTIATION_DIR, name);
    }

    public static void saveListFor(TacletInstantiationModel model) {
        Taclet taclet = model.taclet();
        TacletFindModel tableModel = model.tableModel();
        int start = model.tacletApp().instantiations().size();
        java.util.List<List<String>> instList = getInstantiationListsFor(taclet);
        try (BufferedWriter bw = new BufferedWriter(new FileWriter(
                INSTANTIATION_DIR + File.separator
                        + taclet.name().toString()))) {
            var sb = new StringBuilder();
            for (int i = start; i < tableModel.getRowCount(); i++) {
                if (i > start) {
                    sb.append(SEPARATOR2).append(LINE_END);
                }
                sb.append(tableModel.getValueAt(i, 1)).append(LINE_END);
            }
            String newInst = sb.toString();
            bw.write(newInst);
            final ListIterator<List<String>> instListIt = instList.listIterator();
            int count = 1;
            while (instListIt.hasNext() && count < SAVE_COUNT) {
                final ListIterator<String> instIt = instListIt.next().listIterator();
                sb = new StringBuilder();
                for (int i = 0; instIt.hasNext(); i++) {
                    if (i > 0) {
                        sb.append(SEPARATOR2).append(LINE_END);
                    }
                    sb.append(instIt.next()).append(LINE_END);
                }
                String oldInst = sb.toString();
                if (!oldInst.equals(newInst)) {
                    bw.write(SEPARATOR1 + LINE_END + oldInst);
                    count++;
                }
            }
        } catch (IOException ignored) {
        }
        hm.put(taclet.name().toString(), null);
    }
}
