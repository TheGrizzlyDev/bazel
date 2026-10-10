// Copyright 2018 The Bazel Authors. All rights reserved.
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

package com.google.devtools.build.lib.skyframe.serialization;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNotSame;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertThrows;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

/** Tests automatic codec discovery when a retained loader's classpath changes. */
@RunWith(JUnit4.class)
public final class AutoRegistryTest {
  /** A class available only after the test jar is added to the isolated loader. */
  public static final class AdditionalValue {
    public AdditionalValue() {}
  }

  private static final class MutableClassLoader extends URLClassLoader {
    private URL[] currentClasspath;

    MutableClassLoader(URL[] urls) {
      super(urls, ClassLoader.getPlatformClassLoader());
      currentClasspath = urls.clone();
    }

    void append(URL url) {
      addURL(url);
      currentClasspath = super.getURLs();
    }

    void expose(URL[] urls) {
      currentClasspath = urls.clone();
    }

    @Override
    public URL[] getURLs() {
      return currentClasspath.clone();
    }
  }

  @Test
  public void changingClasspathRediscoversCodecsWhileUnchangedClasspathStaysWarm()
      throws Exception {
    URL testJar = AutoRegistryTest.class.getProtectionDomain().getCodeSource().getLocation();
    List<URL> initialClasspath = new ArrayList<>();
    for (String entry : System.getProperty("java.class.path").split(File.pathSeparator)) {
      URL url = Path.of(entry).toUri().toURL();
      // Bazel may advertise runfiles symlinks while CodeSource uses their resolved paths.
      if (!Files.isSameFile(Path.of(url.toURI()), Path.of(testJar.toURI()))) {
        initialClasspath.add(url);
      }
    }
    try (MutableClassLoader loader =
        new MutableClassLoader(initialClasspath.toArray(URL[]::new))) {
      Class<?> autoRegistry = loader.loadClass(AutoRegistry.class.getName());
      Method getRegistry = autoRegistry.getMethod("get");
      Object initialRegistry = getRegistry.invoke(null);
      assertSame(initialRegistry, getRegistry.invoke(null));

      loader.append(testJar);
      Object value =
          loader.loadClass(AdditionalValue.class.getName()).getConstructor().newInstance();
      Method getCodec =
          initialRegistry.getClass().getMethod("getCodecDescriptorForObject", Object.class);
      InvocationTargetException exception =
          assertThrows(
              InvocationTargetException.class, () -> getCodec.invoke(initialRegistry, value));
      assertEquals(
          SerializationException.NoCodecException.class.getName(),
          exception.getCause().getClass().getName());

      Object refreshedRegistry = getRegistry.invoke(null);
      assertNotSame(initialRegistry, refreshedRegistry);
      assertNotNull(getCodec.invoke(refreshedRegistry, value));
      assertSame(refreshedRegistry, getRegistry.invoke(null));

      // Changing the advertised classpath does not unload classes from the retained loader.
      loader.expose(initialClasspath.toArray(URL[]::new));
      assertSame(value.getClass(), loader.loadClass(AdditionalValue.class.getName()));
      Object contractedRegistry = getRegistry.invoke(null);
      assertNotSame(refreshedRegistry, contractedRegistry);
      assertThrows(
          InvocationTargetException.class, () -> getCodec.invoke(contractedRegistry, value));
      assertSame(contractedRegistry, getRegistry.invoke(null));
    }
  }
}
