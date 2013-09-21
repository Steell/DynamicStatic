using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicStatic;
using NUnit.Framework;

namespace DynamicStaticTests
{
    [TestFixture]
    public class BasicTests
    {
        [Test]
        public void FactorialDefinition()
        {
            Assert.AreEqual("(Atom -> Atom)", DS.type2str(DS.type_check(DS.fact)));
        }
    }
}
