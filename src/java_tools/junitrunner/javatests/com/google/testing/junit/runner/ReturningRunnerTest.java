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
package com.google.testing.junit.runner;

import static org.junit.Assert.assertEquals;

import org.junit.Test;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;

/** The public returning entry preserves one classloader across pass, fail, pass. */
public final class ReturningRunnerTest {
  private static int executions;

  public static void main(String[] args) {
    Result result = JUnitCore.runClasses(ReturningRunnerTest.class);
    result.getFailures().forEach(System.err::println);
    System.exit(result.wasSuccessful() ? 0 : 1);
  }

  @Test
  public void differentSuitesReturnWithoutExiting() {
    String previous = System.getProperty("bazel.test_suite");
    try {
      executions = 0;
      System.setProperty("bazel.test_suite", First.class.getName());
      assertEquals(0, BazelTestRunner.runTests(new String[0]));
      System.setProperty("bazel.test_suite", Failure.class.getName());
      assertEquals(1, BazelTestRunner.runTests(new String[0]));
      System.setProperty("bazel.test_suite", Second.class.getName());
      assertEquals(0, BazelTestRunner.runTests(new String[0]));
      assertEquals(3, executions);
    } finally {
      if (previous == null) {
        System.clearProperty("bazel.test_suite");
      } else {
        System.setProperty("bazel.test_suite", previous);
      }
    }
  }

  public static final class First {
    @Test
    public void first() {
      assertEquals(1, ++executions);
    }
  }

  public static final class Failure {
    @Test
    public void failure() {
      assertEquals(2, ++executions);
      throw new AssertionError("Expected returning test failure");
    }
  }

  public static final class Second {
    @Test
    public void second() {
      assertEquals(3, ++executions);
    }
  }
}
