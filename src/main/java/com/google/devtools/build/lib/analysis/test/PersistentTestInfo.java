// Copyright 2026 The Bazel Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package com.google.devtools.build.lib.analysis.test;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.devtools.build.lib.actions.Artifact;
import com.google.devtools.build.lib.actions.CommandLine;
import com.google.devtools.build.lib.actions.CommandLines;
import com.google.devtools.build.lib.actions.CommandLines.CommandLineAndParamFileInfo;
import com.google.devtools.build.lib.analysis.FilesToRunProvider;
import com.google.devtools.build.lib.analysis.starlark.Args;
import com.google.devtools.build.lib.analysis.starlark.StarlarkRuleContext;
import com.google.devtools.build.lib.cmdline.RepositoryMapping;
import com.google.devtools.build.lib.cmdline.StarlarkThreadContext;
import com.google.devtools.build.lib.collect.nestedset.Depset;
import com.google.devtools.build.lib.collect.nestedset.NestedSet;
import com.google.devtools.build.lib.collect.nestedset.NestedSetBuilder;
import com.google.devtools.build.lib.collect.nestedset.Order;
import com.google.devtools.build.lib.concurrent.ThreadSafety.Immutable;
import com.google.devtools.build.lib.packages.BuiltinProvider;
import com.google.devtools.build.lib.packages.NativeInfo;
import com.google.devtools.build.lib.starlarkbuildapi.CommandLineArgsApi;
import com.google.devtools.build.lib.starlarkbuildapi.FileApi;
import com.google.devtools.build.lib.starlarkbuildapi.StarlarkRuleContextApi;
import com.google.devtools.build.lib.starlarkbuildapi.test.PersistentTestInfoApi;
import com.google.devtools.build.lib.supplier.InterruptibleSupplier;
import javax.annotation.Nullable;
import net.starlark.java.eval.EvalException;
import net.starlark.java.eval.Sequence;
import net.starlark.java.eval.Starlark;
import net.starlark.java.eval.StarlarkList;
import net.starlark.java.eval.StarlarkThread;

/**
 * Provider that enables tests to run in persistent worker processes, avoiding startup overhead for
 * JVM tests and simulators.
 */
@Immutable
public final class PersistentTestInfo extends NativeInfo implements PersistentTestInfoApi {

  /** Singleton instance of the provider type for {@link PersistentTestInfo}. */
  public static final PersistentTestInfoProvider PROVIDER = new PersistentTestInfoProvider();

  private final boolean multiplex;
  private final String requiresWorkerProtocol;
  @Nullable private final String workerKeyMnemonic;
  private final CommandLines workerCommandLines;
  private final CommandLines testCommandLines;
  @Nullable private final FilesToRunProvider workerExecutable;
  @Nullable private final NestedSet<Artifact> workerTools;
  @Nullable private final NestedSet<Artifact> testInputs;

  /**
   * Constructs a new provider with the specified worker configuration.
   *
   * @param multiplex whether the worker can handle multiple concurrent test requests
   * @param requiresWorkerProtocol the protocol format ("proto" or "json")
   * @param workerKeyMnemonic optional mnemonic for flag-based filtering (null if not set)
   * @param workerCommandLines command lines for worker binary arguments
   * @param testCommandLines command lines for test runner arguments
   * @param workerExecutable the persistent worker executable (null if not specified)
   * @param workerTools additional tools required by the worker (null if not specified)
   * @param testInputs test-specific input files (null if not specified)
   */
  public PersistentTestInfo(

      boolean multiplex,
      String requiresWorkerProtocol,
      @Nullable String workerKeyMnemonic,
      CommandLines workerCommandLines,
      CommandLines testCommandLines,
      @Nullable FilesToRunProvider workerExecutable,
      @Nullable NestedSet<Artifact> workerTools,
      @Nullable NestedSet<Artifact> testInputs) {
    this.multiplex = multiplex;
    this.requiresWorkerProtocol = Preconditions.checkNotNull(requiresWorkerProtocol);
    if (!requiresWorkerProtocol.equals("proto") && !requiresWorkerProtocol.equals("json")) {
      throw new IllegalArgumentException(
          "requires_worker_protocol must be either \"proto\" or \"json\", got: "
              + requiresWorkerProtocol);
    }
    // Store null if empty string or null is passed
    this.workerKeyMnemonic =
        (workerKeyMnemonic == null || workerKeyMnemonic.isEmpty()) ? null : workerKeyMnemonic;
    this.workerCommandLines = Preconditions.checkNotNull(workerCommandLines);
    this.testCommandLines = Preconditions.checkNotNull(testCommandLines);
    this.workerExecutable = workerExecutable;
    this.workerTools = workerTools;
    this.testInputs = testInputs;
  }

  @Override
  public PersistentTestInfoProvider getProvider() {
    return PROVIDER;
  }

  /** Returns whether the worker can handle multiple concurrent test requests. */
  @Override
  public Boolean getMultiplex() {
    return multiplex;
  }

  /** Returns the communication protocol format ("proto" or "json"). */
  @Override
  public String getRequiresWorkerProtocol() {
    return requiresWorkerProtocol;
  }

  /**
   * Returns the optional mnemonic for flag-based filtering. Null means the test is always eligible
   * for persistent worker mode.
   */
  @Override
  @Nullable
  public String getWorkerKeyMnemonic() {
    return workerKeyMnemonic;
  }

  /** Returns worker args as a Starlark-visible sequence of Args objects. */
  @Override
  public Sequence<CommandLineArgsApi> getWorkerArgs() {
    ImmutableList.Builder<CommandLineArgsApi> result = ImmutableList.builder();
    ImmutableSet<Artifact> directoryInputs = ImmutableSet.of();
    for (CommandLineAndParamFileInfo cmdLine : workerCommandLines.unpack()) {
      result.add(Args.forRegisteredAction(cmdLine, directoryInputs));
    }
    return StarlarkList.immutableCopyOf(result.build());
  }

  /** Returns the worker CommandLines for internal use during spawn creation. */
  public CommandLines getWorkerCommandLines() {
    return workerCommandLines;
  }

  /** Returns the test arguments as a Starlark-visible sequence of Args objects. */
  @Override
  public Sequence<CommandLineArgsApi> getTestArgs() {
    ImmutableList.Builder<CommandLineArgsApi> result = ImmutableList.builder();
    // Empty set since test arguments typically don't involve directory artifacts
    ImmutableSet<Artifact> directoryInputs = ImmutableSet.of();

    for (CommandLineAndParamFileInfo cmdLine : testCommandLines.unpack()) {
      result.add(Args.forRegisteredAction(cmdLine, directoryInputs));
    }
    return StarlarkList.immutableCopyOf(result.build());
  }

  /** Returns the test CommandLines for internal use during spawn creation. */
  public CommandLines getTestCommandLines() {
    return testCommandLines;
  }

  /**
   * Returns the worker executable, or null if not specified.
   */
  @Nullable
  public FilesToRunProvider getWorkerExecutable() {
    return workerExecutable;
  }

  /** Returns worker tools as a Depset for Starlark, or null if not specified. */
  @Override
  @Nullable
  public Depset getWorkerToolsForStarlark() {
    return workerTools != null ? Depset.of(Artifact.class, workerTools) : null;
  }

  /** Returns the worker tools for internal use, or null if not specified. */
  @Nullable
  public NestedSet<Artifact> getWorkerTools() {
    return workerTools;
  }

  /** Returns the test-specific inputs, or null if not specified. */
  @Nullable
  public NestedSet<Artifact> getTestInputs() {
    return testInputs;
  }

  /** Returns the test inputs as a Depset for Starlark. */
  @Override
  @Nullable
  public Depset getTestInputsForStarlark() {
    return testInputs != null ? Depset.of(Artifact.class, testInputs) : null;
  }

  /** Provider implementation for {@link PersistentTestInfoApi}. */
  public static class PersistentTestInfoProvider extends BuiltinProvider<PersistentTestInfo>
      implements PersistentTestInfoApi.PersistentTestInfoApiProvider {

    private PersistentTestInfoProvider() {
      super("PersistentTestInfo", PersistentTestInfo.class);
    }

    @Override
    public PersistentTestInfoApi constructor(
            StarlarkRuleContextApi ctx,
        Boolean multiplex,
        String requiresWorkerProtocol,
        @Nullable String workerKeyMnemonic,
        Sequence<?> workerArgs,
        Sequence<?> testArgs,
        @Nullable Object workerExecutableUnchecked,
        @Nullable Object workerToolsUnchecked,
        @Nullable Object testInputsUnchecked,
        StarlarkThread thread)
        throws EvalException {
      // Validate protocol
      if (!requiresWorkerProtocol.equals("proto") && !requiresWorkerProtocol.equals("json")) {
        throw new EvalException(
            "requires_worker_protocol must be either \"proto\" or \"json\", got: "
                + requiresWorkerProtocol);
      }

      // Validate and extract worker executable
      FilesToRunProvider workerExec = null;
      if (workerExecutableUnchecked != null) {
        if (workerExecutableUnchecked instanceof Artifact workerExecutableArtifact) {
          StarlarkRuleContext starlarkRuleContext = (StarlarkRuleContext) ctx;
          workerExec = starlarkRuleContext.getExecutableRunfiles(workerExecutableArtifact, "worker_executable");
        } else if (workerExecutableUnchecked instanceof FilesToRunProvider workerExecutableFiles) {
          workerExec = workerExecutableFiles;
        } else {
          throw new EvalException(
                  "worker_executable must be a File or FilesToRunProvider, got: "
                          + Starlark.type(workerExecutableUnchecked));
        }
      }

      // Validate and extract worker tools
      NestedSet<Artifact> workerToolsSet = null;
      if (workerToolsUnchecked != null && workerToolsUnchecked != Starlark.NONE) {
        if (workerToolsUnchecked instanceof Sequence) {
          // Process sequence: can contain Files or FilesToRunProviders
          Sequence<?> toolsSeq = (Sequence<?>) workerToolsUnchecked;
          NestedSetBuilder<Artifact> builder = NestedSetBuilder.stableOrder();

          for (Object tool : toolsSeq) {
            if (tool instanceof Artifact) {
              builder.add((Artifact) tool);
              // Also check if this artifact has runfiles
              if (ctx instanceof StarlarkRuleContext) {
                StarlarkRuleContext starlarkRuleContext = (StarlarkRuleContext) ctx;
                FilesToRunProvider provider =
                    starlarkRuleContext.getExecutableRunfiles((Artifact) tool, "worker_tools");
                if (provider != null) {
                  builder.addTransitive(provider.getFilesToRun());
                }
              }
            } else if (tool instanceof FilesToRunProvider) {
              builder.addTransitive(((FilesToRunProvider) tool).getFilesToRun());
            } else {
              throw new EvalException(
                  "worker_tools must contain Files or FilesToRunProvider instances, got: "
                      + Starlark.type(tool));
            }
          }
          workerToolsSet = builder.build();
        } else if (workerToolsUnchecked instanceof Depset) {
          workerToolsSet = Depset.cast(workerToolsUnchecked, Artifact.class, "worker_tools");
        } else {
          throw new EvalException(
              "worker_tools must be a sequence or depset, got: "
                  + Starlark.type(workerToolsUnchecked));
        }
      }

      // Validate and extract test inputs. Treat an empty sequence/depset as
      // "unset" so callers can pass the empty default without inadvertently
      // clobbering the action's real input closure downstream.
      NestedSet<Artifact> testInputsSet = null;
      if (testInputsUnchecked instanceof Sequence) {
        Sequence<Artifact> inputs = Sequence.cast(testInputsUnchecked, Artifact.class, "inputs");
        if (!inputs.isEmpty()) {
          testInputsSet = NestedSetBuilder.wrap(Order.STABLE_ORDER, inputs);
        }
      } else if (testInputsUnchecked != null) {
        NestedSet<Artifact> asDepset = Depset.cast(testInputsUnchecked, Artifact.class, "inputs");
        if (!asDepset.isEmpty()) {
          testInputsSet = asDepset;
        }
      }

      // Get RepositoryMapping from thread context
      StarlarkThreadContext threadContext = thread.getThreadLocal(StarlarkThreadContext.class);
      InterruptibleSupplier<RepositoryMapping> repoMappingSupplier;
      if (threadContext != null) {
        repoMappingSupplier = () -> threadContext.getMainRepoMapping();
      } else {
        // Fallback for contexts without thread context
        repoMappingSupplier = () -> null;
      }

      // Build CommandLines for worker_args
      CommandLines workerCommandLines =
          buildCommandLines(workerArgs, repoMappingSupplier, "worker_args");

      // Build CommandLines for test_args
      CommandLines testCommandLines = buildCommandLines(testArgs, repoMappingSupplier, "test_args");

      return new PersistentTestInfo(
          multiplex,
          requiresWorkerProtocol,
          workerKeyMnemonic,
          workerCommandLines,
          testCommandLines,
          workerExec,
          workerToolsSet,
          testInputsSet);
    }

    /**
     * Helper method to build CommandLines from a Sequence of strings or Args objects.
     *
     * @param args the sequence of arguments (strings or Args objects)
     * @param repoMappingSupplier supplier for repository mapping
     * @param fieldName name of the field (for error messages)
     * @return the built CommandLines
     * @throws EvalException if the arguments contain invalid types
     */
    private static CommandLines buildCommandLines(
        Sequence<?> args,
        InterruptibleSupplier<RepositoryMapping> repoMappingSupplier,
        String fieldName)
        throws EvalException {
      CommandLines.Builder builder = CommandLines.builder();
      ImmutableList.Builder<String> stringArgs = null;

      for (Object arg : args) {
        if (arg instanceof String) {
          if (stringArgs == null) {
            stringArgs = ImmutableList.builder();
          }
          stringArgs.add((String) arg);
        } else if (arg instanceof Args) {
          // Flush any accumulated strings first
          if (stringArgs != null) {
            builder.addCommandLine(CommandLine.of(stringArgs.build()));
            stringArgs = null;
          }
          // Add the Args object's command line
          Args argsObj = (Args) arg;
          try {
            builder.addCommandLine(argsObj.build(repoMappingSupplier), argsObj.getParamFileInfo());
          } catch (InterruptedException e) {
            throw new EvalException("Interrupted while building arguments", e);
          }
        } else {
          throw new EvalException(
              fieldName
                  + " must contain only strings or Args objects, got: "
                  + Starlark.type(arg));
        }
      }

      // Flush any remaining strings
      if (stringArgs != null) {
        builder.addCommandLine(CommandLine.of(stringArgs.build()));
      }

      return builder.build();
    }
  }
}
