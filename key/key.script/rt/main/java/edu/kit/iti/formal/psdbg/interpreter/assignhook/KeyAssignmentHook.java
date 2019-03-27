package edu.kit.iti.formal.psdbg.interpreter.assignhook;

import com.google.common.base.Converter;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import edu.kit.iti.formal.psdbg.interpreter.data.KeyData;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.math.BigInteger;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

import static de.uka.ilkd.key.strategy.StrategyProperties.*;

/**
 * @author Alexander Weigl
 * @version 1 (21.08.17)
 */
public class KeyAssignmentHook extends DefaultAssignmentHook<KeyData> {
    private static Logger logger = LogManager.getLogger(KeyAssignmentHook.class);

    public KeyAssignmentHook() {
        register("__KEY_MAX_STEPS",
                "Should be a positive number and is the limit for rule application in automatic proof searchs.\n",
                (kd, val) -> {
                    try {
                        kd.getProof().getSettings().getStrategySettings().setMaxSteps(
                                ((BigInteger) val.getData()).intValue()
                        );
                    } catch (ClassCastException e) {
                        return false;
                    }
                    return true;
                },
                (kd) -> Value.from(kd.getProof().getSettings().getStrategySettings().getMaxSteps()));

        register("__KEY_TIMEOUT",
                (kd, val) -> {
                    try {
                        kd.getProof().getSettings().getStrategySettings().setTimeout(
                                ((BigInteger) val.getData()).longValue()
                        );
                    } catch (ClassCastException e) {
                        return false;
                    }
                    return true;
                },
                (kd) -> Value.from(BigInteger.valueOf(kd.getProof().getSettings().getStrategySettings().getTimeout())));

        /*TODO        register("__KEY_CHOICE", ((keyData, value) -> {
                keyData.getProof().getSettings().getChoiceSettings().getChoices()
        }), keyData -> {

        })
        */

        this.registerSMTPD("INVARIANT_ALL",
                "",
                (ss) -> Value.from(ss.invariantForall),
                ((ss, val) -> ss.invariantForall = val));

        this.registerSMTPD("MAX_GENERIC_SORTS", "",
                (ss) -> Value.from(ss.maxGenericSorts),
                (ss, v) -> ss.maxGenericSorts = v.intValue());

        this.registerSMTPD("MAX_INTEGER", "",
                (ss) -> Value.from(ss.maxInteger),
                (ss, v) -> ss.maxInteger = v.intValue());

        this.registerSMTPD("MIN_INTEGER", "",
                (ss) -> Value.from(ss.minInteger),
                (ss, v) -> ss.minInteger = v.intValue());

        this.registerSMTPD("USE_BUILTIN_UNIQUENESS", "",
                (ss) -> Value.from(ss.useBuiltInUniqueness),
                (ss, v) -> ss.useBuiltInUniqueness = v);

        this.registerSMTPD("USE_CONSTANTS_FOR_INTEGERS", "",
                (ss) -> Value.from(ss.useConstantsForIntegers),
                (ss, v) -> ss.useConstantsForIntegers = v);

        this.registerSMTPD("useExplicitTypeHierarchy", "",
                (ss) -> Value.from(ss.useExplicitTypeHierarchy),
                (ss, v) -> ss.useExplicitTypeHierarchy = v);

        this.registerSMTPD("useNullInstantiation", "",
                (ss) -> Value.from(ss.useNullInstantiation),
                (ss, v) -> ss.useNullInstantiation = v);

        this.registerSMTPD("USE_UI_MULTIPLICATION", "",
                (ss) -> Value.from(ss.useUIMultiplication),
                (ss, v) -> ss.useUIMultiplication = v);

        registerSMTPI("ACTIVE_SOLVER", "",
                (ss) -> Value.from(ss.activeSolver),
                (ss, v) -> ss.activeSolver = v);

        registerSMTPI("CHECK_FOR_SUPPORT", "",
                (ss) -> Value.from(ss.checkForSupport),
                (ss, v) -> ss.checkForSupport = v);

        registerSMTPI("heapBound", "",
                (ss) -> Value.from(ss.heapBound),
                (ss, v) -> ss.heapBound = v.intValue());

        registerSMTPI("INT_BOUND", "",
                (ss) -> Value.from(ss.intBound),
                (ss, v) -> ss.intBound = v.intValue());

        registerSMTPI("LOCSET_BOUND", "",
                (ss) -> Value.from(ss.locsetBound),
                (ss, v) -> ss.locsetBound = v.intValue());

        registerSMTPI("MAX_CONCURRENT_PROCESSES", "",
                (ss) -> Value.from(ss.maxConcurrentProcesses),
                (ss, v) -> ss.maxConcurrentProcesses = v.intValue());

        registerSMTPI("MODE_OF_PROGRESS_DIALOG", "",
                (ss) -> Value.from(ss.modeOfProgressDialog),
                (ss, v) -> ss.modeOfProgressDialog = v.intValue());

        registerSMTPI("OBJECT_BOUND", "",
                (ss) -> Value.from(ss.objectBound),
                (ss, v) -> ss.objectBound = v.intValue());

        registerSMTPI("PATH_FOR_SMT_TRANSLATION", "",
                (ss) -> Value.from(ss.pathForSMTTranslation),
                (ss, v) -> ss.pathForSMTTranslation = v);

        registerSMTPI("SEQ_BOUND", "",
                (ss) -> Value.from(ss.seqBound),
                (ss, v) -> ss.seqBound = v.intValue());

        registerSMTPI("SHOW_RESULTS_AFTER_EXECUTION", "",
                (ss) -> Value.from(ss.showResultsAfterExecution),
                (ss, v) -> ss.showResultsAfterExecution = v);

        registerSMTPI("STORE_TRANSLATION_TO_FILE", "",
                (ss) -> Value.from(ss.storeSMTTranslationToFile),
                (ss, v) -> ss.storeSMTTranslationToFile = v);

        registerSMTPI("TIMEOUT", "",
                (ss) -> Value.from(ss.timeout),
                (ss, v) -> ss.timeout = v.intValue());

        BiMap<String, String> methodMap = HashBiMap.create(3);
        methodMap.put("method", METHOD_CONTRACT);
        methodMap.put("expand", METHOD_EXPAND);
        methodMap.put("none", METHOD_NONE);
        registerKeYMultiOptions("__KEY_METHOD_OPTION", METHOD_OPTIONS_KEY, Maps.asConverter(methodMap));

        BiMap<String, String> nonLinArithMap = HashBiMap.create(3);
        nonLinArithMap.put("completion", NON_LIN_ARITH_COMPLETION);
        nonLinArithMap.put("defops", NON_LIN_ARITH_DEF_OPS);
        nonLinArithMap.put("none", NON_LIN_ARITH_NONE);
        registerKeYMultiOptions("__KEY_NON_LINEAR_ARITHMETIC", NON_LIN_ARITH_OPTIONS_KEY,
                Maps.asConverter(nonLinArithMap));

        BiMap<String, String> stopModeMap = HashBiMap.create(3);
        stopModeMap.put("nonclose", STOPMODE_NONCLOSE);
        stopModeMap.put("default", STOPMODE_DEFAULT);
        registerKeYMultiOptions("__KEY_STOP_MODE", STOPMODE_OPTIONS_KEY, Maps.asConverter(stopModeMap));

        registerKeYOnOffOption("__KEY_DEP", DEP_OPTIONS_KEY, DEP_ON, DEP_OFF);
        registerKeYOnOffOption("__KEY_QUERY", QUERY_OPTIONS_KEY, QUERY_ON, QUERY_OFF);
    }

    private <K> Variable registerSMTPI(String name, String doc, Function<ProofIndependentSMTSettings, Value<K>> init,
                                       BiConsumer<ProofIndependentSMTSettings, K> setter) {
        BiFunction<KeyData, Value<K>, Boolean> s = ((KeyData keyData, Value<K> value) -> {
            try {
                ProofIndependentSMTSettings ss = ProofIndependentSMTSettings.getDefaultSettingsData();
                setter.accept(ss, (K) value.getData());
                return true;
            } catch (ClassCastException e) {
                return false;
            }
        });
        Function<KeyData, Value<K>> i = (KeyData keyData) -> init.apply(ProofIndependentSMTSettings.getDefaultSettingsData());
        return register("__KEY_SMT__" + name, doc, s, i);
    }

    private <K> Variable registerSMTPD(String name, String doc, Function<ProofDependentSMTSettings, Value<K>> init,
                                       BiConsumer<ProofDependentSMTSettings, K> setter) {
        BiFunction<KeyData, Value<K>, Boolean> s = ((KeyData keyData, Value<K> value) -> {
            try {
                ProofDependentSMTSettings ss = keyData.getProof().getSettings().getSMTSettings();
                setter.accept(ss, value.getData());
                return true;
            } catch (ClassCastException e) {
                return false;
            }
        });
        Function<KeyData, Value<K>> i = (KeyData keyData) -> init.apply(keyData.getProof().getSettings().getSMTSettings());
        return register("__KEY_SMT__" + name, doc, s, i);
    }

    private void registerKeYMultiOptions(String name, String key, Converter<String, String> map) {
        Function<KeyData, Value<String>> init = keyData -> Value.from(map.reverse().convert(keyData.getActiveStrategyProperties().getProperty(key)));
        BiFunction<KeyData, Value<String>, Boolean> setter = (kd, val) -> {
            try {
                kd.getActiveStrategyProperties().setProperty(key, map.convert((String) val.getData()));
            } catch (ClassCastException e) {
                return false;
            }
            return true;
        };
        register(name, setter, init);
    }

    private void registerKeYOnOffOption(String name, String key, String on, String off) {
        Function<KeyData, Value<Boolean>> init = keyData -> Value.from(on.equals(keyData.getActiveStrategyProperties().getProperty(key)));
        BiFunction<KeyData, Value<Boolean>, Boolean> setter = (keyData, value) -> {
            keyData.getActiveStrategyProperties().setProperty(key,
                    value.getData() ? on : off
            );
            return true;
        };
        register(name, setter, init);
    }
}
