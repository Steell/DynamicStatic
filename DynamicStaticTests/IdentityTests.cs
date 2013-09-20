using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.FSharp.Collections;
using NUnit.Framework;

using DynamicStatic;

namespace DynamicStaticTests
{
    [TestFixture]
    public class IdentityTests
    {
        [Test]
        public void Identity()
        {
            var idType = DS.type_check(DS.id);
            Assert.AreEqual("('a -> 'a)", DS.type2str(idType));
        }

        [Test]
        public void AtomCall()
        {
            var idCall1 = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(DS.Type.Atom));

            Assert.AreEqual("Atom", DS.type2str(DS.type_check(idCall1)));
        }

        [Test]
        public void AnyCall()
        {
            var idCall2 = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(DS.Type.Any));

            Assert.AreEqual("Any", DS.type2str(DS.type_check(idCall2)));
        }

        [Test]
        public void UnionCall()
        {
            var idCall3 = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(
                    DS.Type.NewUnion(
                        SetModule.OfSeq(
                            new List<DS.Type> { DS.Type.True, DS.Type.False }))));

            Assert.AreEqual("{True|False}", DS.type2str(DS.type_check(idCall3)));
        }

        [Test]
        public void FunctionCall()
        {
            var idCall4 = DS.TypeExpression.NewCall(
                DS.id, 
                DS.TypeExpression.NewFun(
                    "y", 
                    DS.TypeExpression.NewType_E(DS.Type.NewPolyType("y"))));

            Assert.AreEqual("('a -> 'a)", DS.type2str(DS.type_check(idCall4)));
        }

        [Test]
        public void ListCall()
        {
            var idCall = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(
                    DS.Type.NewList(DS.Type.Atom)));

            Assert.AreEqual("List<Atom>", DS.type2str(DS.type_check(idCall)));
        }

        [Test]
        public void PolyCall()
        {
            var idCall = DS.TypeExpression.NewCall(
                DS.id,
                DS.TypeExpression.NewType_E(DS.Type.NewPolyType("_1_")));

            Assert.AreEqual("'a", DS.type2str(DS.type_check(idCall)));
        }
    }
}
