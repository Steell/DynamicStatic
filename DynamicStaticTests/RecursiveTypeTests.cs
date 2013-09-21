using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicStatic;
using NUnit.Framework;

namespace DynamicStaticTests
{
    [TestFixture]
    public class RecursiveTypeTests
    {
        [Test]
        public void OmegaDefinition()
        {
            Assert.AreEqual("('a -> 'b) where 'a = ('a -> 'b)", DS.type2str(DS.type_check(DS.omega)));
        }

        [Test]
        public void YDefinition()
        {
            Assert.AreEqual("((('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b))", DS.type2str(DS.type_check(DS.yComb)));
        }

        [Test]
        public void Y_FactorialDefinition()
        {
            Assert.AreEqual("(Atom -> Atom)", DS.type2str(DS.type_check(DS.factY)));
        }
    }
}
