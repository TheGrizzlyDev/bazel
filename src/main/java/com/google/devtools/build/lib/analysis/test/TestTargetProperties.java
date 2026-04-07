// Copyright 2014 The Bazel Authors. All rights reserved.
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
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;
import com.google.devtools.build.lib.actions.ExecutionRequirements;
import com.google.devtools.build.lib.actions.ExecutionRequirements.ParseableRequirement.ValidationException;
import com.google.devtools.build.lib.actions.ResourceSet;
import com.google.devtools.build.lib.actions.UserExecException;
import com.google.devtools.build.lib.analysis.RuleContext;
import com.google.devtools.build.lib.cmdline.Label;
import com.google.devtools.build.lib.packages.Rule;
import com.google.devtools.build.lib.packages.TargetUtils;
import com.google.devtools.build.lib.packages.TestSize;
import com.google.devtools.build.lib.packages.TestTimeout;
import com.google.devtools.build.lib.packages.Type;
import com.google.devtools.build.lib.server.FailureDetails.FailureDetail;
import com.google.devtools.build.lib.server.FailureDetails.TestAction;
import com.google.devtools.build.lib.server.FailureDetails.TestAction.Code;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Container for test target properties available to the
 * TestRunnerAction instance.
 */
public class TestTargetProperties {

  /**
   * Resources used by local tests of various sizes.
   *
   * <p>When changing these values, remember to update the documentation at
   * attributes/test/size.html.
   */
  private static final ResourceSet SMALL_RESOURCES = ResourceSet.create(20, 1, 1);
  private static final ResourceSet MEDIUM_RESOURCES = ResourceSet.create(100, 1, 1);
  private static final ResourceSet LARGE_RESOURCES = ResourceSet.create(300, 1, 1);
  private static final ResourceSet ENORMOUS_RESOURCES = ResourceSet.create(800, 1, 1);
  private static final ResourceSet LOCAL_TEST_JOBS_BASED_RESOURCES =
      ResourceSet.createWithLocalTestCount(1);

  private static ResourceSet getResourceSetFromSize(TestSize size) {
    switch (size) {
      case SMALL: return SMALL_RESOURCES;
      case MEDIUM: return MEDIUM_RESOURCES;
      case LARGE: return LARGE_RESOURCES;
      default: return ENORMOUS_RESOURCES;
    }
  }

  private final TestSize size;
  private final TestTimeout timeout;
  private final ImmutableList<String> tags;
  private final boolean isRemotable;
  private final boolean isFlaky;
  private final boolean isExternal;
  private final String language;
  private final ImmutableMap<String, String> executionInfo;
  private final TestConfiguration testConfiguration;

  /**
   * Creates test target properties instance. Constructor expects that it will be called only for
   * test configured targets.
   */
  TestTargetProperties(
      RuleContext ruleContext,
      ExecutionInfo executionRequirements,
      ImmutableMap<String, String> testExecProperties) {
    Rule rule = ruleContext.getRule();

    Preconditions.checkState(TargetUtils.isTestRule(rule));
    size = TestSize.getTestSize(rule);
    timeout = TestTimeout.getTestTimeout(rule);
    tags = ImmutableList.copyOf(ruleContext.attributes().get("tags", Type.STRING_LIST));

    // We need to use method on ruleConfiguredTarget to perform validation.
    isFlaky = ruleContext.attributes().get("flaky", Type.BOOLEAN);
    isExternal = TargetUtils.isExternalTestRule(rule);

    Map<String, String> executionInfo = Maps.newLinkedHashMap();
    executionInfo.putAll(TargetUtils.getExecutionInfo(rule));
    executionInfo.putAll(testExecProperties);

    boolean incompatibleExclusiveTestSandboxed = false;

    testConfiguration = ruleContext.getFragment(TestConfiguration.class);
    if (testConfiguration != null) {
      incompatibleExclusiveTestSandboxed = testConfiguration.incompatibleExclusiveTestSandboxed();
    }

    if (incompatibleExclusiveTestSandboxed) {
      if (TargetUtils.isLocalTestRule(rule)) {
        executionInfo.put(ExecutionRequirements.LOCAL, "");
      } else if (TargetUtils.isExclusiveTestRule(rule)) {
        executionInfo.put(ExecutionRequirements.NO_REMOTE_EXEC, "");
      }
    } else {
      if (TargetUtils.isLocalTestRule(rule) || TargetUtils.isExclusiveTestRule(rule)) {
        executionInfo.put(ExecutionRequirements.LOCAL, "");
      }
    }

    if (TargetUtils.isNoTestloasdTestRule(rule)) {
      executionInfo.put(ExecutionRequirements.LOCAL, "");
      executionInfo.put(ExecutionRequirements.NO_TESTLOASD, "");
    }

    if (executionRequirements != null) {
      // This will overwrite whatever TargetUtils put there, which might be confusing.
      executionInfo.putAll(executionRequirements.getExecutionInfo());
    }
    ruleContext.getConfiguration().modifyExecutionInfo(executionInfo, TestRunnerAction.MNEMONIC);
    this.executionInfo = ImmutableMap.copyOf(executionInfo);

    isRemotable =
        !executionInfo.containsKey(ExecutionRequirements.LOCAL)
            && !executionInfo.containsKey(ExecutionRequirements.NO_REMOTE)
            && !executionInfo.containsKey(ExecutionRequirements.NO_REMOTE_EXEC);

    language = TargetUtils.getRuleLanguage(rule);
  }

  private TestTargetProperties(
      TestSize size,
      TestTimeout timeout,
      ImmutableList<String> tags,
      boolean isFlaky,
      boolean isExternal,
      TestConfiguration testConfiguration,
      ImmutableMap<String, String> executionInfo,
      boolean isRemotable,
      String language) {
    this.size = size;
    this.timeout = timeout;
    this.tags = tags;
    this.isFlaky = isFlaky;
    this.isExternal = isExternal;
    this.testConfiguration = testConfiguration;
    this.executionInfo = executionInfo;
    this.isRemotable = isRemotable;
    this.language = language;
  }

  public TestSize getSize() {
    return size;
  }

  public TestTimeout getTimeout() {
    return timeout;
  }

  public List<String> getTags() {
    return tags;
  }

  public boolean isRemotable() {
    return isRemotable;
  }

  public boolean isFlaky() {
    return isFlaky;
  }

  public boolean isExternal() {
    return isExternal;
  }

  private static Map<String, Double> parseTags(Label label, Map<String, String> tags)
      throws UserExecException {
    Map<String, Double> resources = new HashMap<>();
    ExecutionRequirements.ParseableRequirement requirement;
    for (String tag : tags.keySet()) {
      String resource;
      String amount;
      requirement = ExecutionRequirements.RESOURCES;
      try {
        String value = requirement.parseIfMatches(tag);
        if (value != null) {
          int splitIndex = value.indexOf(":");
          resource = value.substring(0, splitIndex);
          amount = value.substring(splitIndex + 1);
        } else {
          requirement = ExecutionRequirements.CPU;
          value = requirement.parseIfMatches(tag);
          resource = ResourceSet.CPU;
          amount = value;
        }
        if (value != null) {
          if (resources.get(resource) != null) {
            String message =
                String.format(
                    "%s has more than one tag for resource '%s', but duplicate tags aren't allowed",
                    label, resource);
            throw new UserExecException(createFailureDetail(message, Code.DUPLICATE_CPU_TAGS));
          }
          resources.put(resource, Double.parseDouble(amount));
        }
      } catch (ValidationException e) {
        String message =
            String.format(
                "%s has a '%s' tag, but its value '%s' didn't pass validation: %s",
                label, requirement.userFriendlyName(), e.getTagValue(), e.getMessage());
        throw new UserExecException(createFailureDetail(message, Code.INVALID_CPU_TAG));
      }
    }
    return resources;
  }

  public ResourceSet getLocalResourceUsage(Label label, boolean usingLocalTestJobs)
      throws UserExecException {
    if (usingLocalTestJobs) {
      return LOCAL_TEST_JOBS_BASED_RESOURCES;
    }

    ResourceSet defaultResources = getResourceSetFromSize(size);
    Map<String, Double> resourcesFromTags = parseTags(label, executionInfo);
    Map<String, Double> configResources =
        testConfiguration == null ? ImmutableMap.of() : testConfiguration.getTestResources(size);
    if (resourcesFromTags.isEmpty() && configResources.isEmpty()) {
      return defaultResources;
    }

    return ResourceSet.create(
        ImmutableMap.<String, Double>builder()
            .putAll(defaultResources.getResources())
            .putAll(configResources)
            .putAll(resourcesFromTags)
            .buildKeepingLast(),
        defaultResources.getLocalTestCount());
  }

  private static FailureDetail createFailureDetail(String message, Code detailedCode) {
    return FailureDetail.newBuilder()
        .setMessage(message)
        .setTestAction(TestAction.newBuilder().setCode(detailedCode))
        .build();
  }

  /**
   * Returns a map of execution info. See {@link
   * com.google.devtools.build.lib.actions.Spawn#getExecutionInfo}.
   */
  public ImmutableMap<String, String> getExecutionInfo() {
    return executionInfo;
  }

  public String getLanguage() {
    return language;
  }

  private static final Pattern SHARD_EXEC_INFO = Pattern.compile("(.*)\\.run\\[(\\d+)%\\]$");

  /**
   * Returns a copy of this {@link TestTargetProperties}, but with execution info potentially
   * filtered based on the run id and count.
   */
  public TestTargetProperties filterForRun(int run, int totalRuns) {
    ImmutableMap.Builder<String, String> filteredExecutionInfo = new ImmutableMap.Builder<>();
    for (Map.Entry<String, String> entry : executionInfo.entrySet()) {
      Matcher matcher = SHARD_EXEC_INFO.matcher(entry.getKey());
      if (matcher.find()) {
        // Filter out based on the run count.
        String propName = matcher.group(1);
        int percent = Integer.parseInt(matcher.group(2));
        String propValue = entry.getValue();

        // Only include the filtered name if the check passes
        if ((run * 100 / totalRuns) <= percent) {
          filteredExecutionInfo.put(propName, propValue);
        }
      } else {
        filteredExecutionInfo.put(entry);
      }
    }
    return new TestTargetProperties(
        size,
        timeout,
        tags,
        isFlaky,
        isExternal,
        testConfiguration,
        filteredExecutionInfo.build(),
        isRemotable,
        language);
  }
}
